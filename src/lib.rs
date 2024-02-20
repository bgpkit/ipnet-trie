//! This crate provides storage and retrieval of IPv4 and IPv6 network prefixes.
//!
//! Currently, it uses `ipnet` crate, that provides IP network data structure and
//! `prefix-trie` as backend, that provides fast lookup times, and a small memory footprint.
//! Backend can be changed in future releases.
//!
//! ## Examples
//!
//! ```rust
//! use std::net::{IpAddr, Ipv6Addr};
//! use ipnet::{IpNet, Ipv6Net};
//! use ipnet_trie::IpnetTrie;
//!
//! let mut table = IpnetTrie::new();
//! let network = IpNet::from(Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap());
//! let ip_address = Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0x1);
//!
//! assert_eq!(table.insert(network, "foo"), None);
//! // Get value for network from table
//! assert_eq!(table.longest_match(&IpNet::from(ip_address.to_canonical())), Some((network, &"foo")));
//! ```

#![doc(
    html_logo_url = "https://raw.githubusercontent.com/bgpkit/assets/main/logos/icon-transparent.png",
    html_favicon_url = "https://raw.githubusercontent.com/bgpkit/assets/main/logos/favicon.ico"
)]

#[cfg(feature = "export")]
mod export;

use ipnet::{IpNet, Ipv4Net, Ipv6Net};
use prefix_trie::PrefixMap;
use std::collections::HashSet;

/// Table holding IPv4 and IPv6 network prefixes with value.
#[derive(Default)]
pub struct IpnetTrie<T> {
    ipv4: PrefixMap<Ipv4Net, T>,
    ipv6: PrefixMap<Ipv6Net, T>,
}

impl<T> Clone for IpnetTrie<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            ipv4: self.ipv4.clone(),
            ipv6: self.ipv6.clone(),
        }
    }
}

impl<T: Clone> IpnetTrie<T> {
    /// Count the number of unique IPv4 and IPv6 addresses in the trie.
    ///
    /// ```rust
    /// use std::str::FromStr;
    /// use ipnet::{Ipv4Net, Ipv6Net};
    /// use ipnet_trie::IpnetTrie;
    ///
    /// let mut table = IpnetTrie::new();
    /// table.insert(Ipv4Net::from_str("192.0.2.129/25").unwrap(), 1);
    /// table.insert(Ipv4Net::from_str("192.0.2.0/24").unwrap(), 1);
    /// table.insert(Ipv4Net::from_str("192.0.2.0/24").unwrap(), 1);
    /// table.insert(Ipv4Net::from_str("192.0.2.0/24").unwrap(), 1);
    /// assert_eq!(table.ip_count(), (256, 0));
    ///
    /// table.insert(Ipv4Net::from_str("198.51.100.0/25").unwrap(), 1);
    /// table.insert(Ipv4Net::from_str("198.51.100.64/26").unwrap(), 1);
    /// assert_eq!(table.ip_count(), (384, 0));
    ///
    /// table.insert(Ipv4Net::from_str("198.51.100.65/26").unwrap(), 1);
    /// assert_eq!(table.ip_count(), (384, 0));
    ///
    /// table.insert(Ipv6Net::from_str("2001:DB80::/48").unwrap(), 1);
    /// assert_eq!(table.ip_count(), (384, 2_u128.pow(80)));
    /// table.insert(Ipv6Net::from_str("2001:DB80::/49").unwrap(), 1);
    /// assert_eq!(table.ip_count(), (384, 2_u128.pow(80)));
    /// table.insert(Ipv6Net::from_str("2001:DB81::/48").unwrap(), 1);
    /// assert_eq!(table.ip_count(), (384, 2_u128.pow(81)));
    /// ```
    pub fn ip_count(&self) -> (u32, u128) {
        let mut new_trie = self.clone();

        let mut root_ipv4_prefixes: HashSet<Ipv4Net> = HashSet::new();
        let mut root_ipv6_prefixes: HashSet<Ipv6Net> = HashSet::new();

        loop {
            let mut v4_iter = new_trie.ipv4.iter();
            match v4_iter.next() {
                Some((net, _data)) => {
                    let root_prefix = new_trie.ipv4.get_spm_prefix(net).unwrap().clone();
                    root_ipv4_prefixes.insert(root_prefix);
                    new_trie.ipv4.remove_children(&root_prefix);
                }
                None => {
                    break;
                }
            }
        }

        loop {
            let mut v6_iter = new_trie.ipv6.iter();
            match v6_iter.next() {
                Some((net, _data)) => {
                    let root_prefix = new_trie.ipv6.get_spm_prefix(net).unwrap().clone();
                    root_ipv6_prefixes.insert(root_prefix);
                    new_trie.ipv6.remove_children(&root_prefix);
                }
                None => {
                    break;
                }
            }
        }

        let mut ipv4_space: u32 = 0;
        let mut ipv6_space: u128 = 0;

        for prefix in root_ipv4_prefixes {
            ipv4_space += 2u32.pow(32 - prefix.prefix_len() as u32);
        }
        for prefix in root_ipv6_prefixes {
            ipv6_space += 2u128.pow(128 - prefix.prefix_len() as u32);
        }

        (ipv4_space, ipv6_space)
    }
}

impl<T> IpnetTrie<T> {
    /// Constructs a new, empty `IpnetTrie<T>`.
    pub fn new() -> Self {
        Self {
            ipv4: PrefixMap::new(),
            ipv6: PrefixMap::new(),
        }
    }

    /// Returns the number of elements in the table. First value is number of IPv4 networks and second is number of IPv6 networks.
    pub fn len(&self) -> (usize, usize) {
        (self.ipv4.iter().count(), self.ipv6.iter().count())
    }

    /// Returns `true` if table is empty.
    pub fn is_empty(&self) -> bool {
        self.ipv4.iter().next().is_none() && self.ipv6.iter().next().is_none()
    }

    /// Insert a value for the `IpNet`. If prefix existed previously, the old value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ipnet_trie::IpnetTrie;
    /// use ipnet::Ipv6Net;
    /// use std::net::Ipv6Addr;
    ///
    /// let mut table = IpnetTrie::new();
    /// let network = Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    ///
    /// assert_eq!(table.insert(network, "foo"), None);
    /// // Insert duplicate
    /// assert_eq!(table.insert(network, "bar"), Some("foo"));
    /// // Value is replaced
    /// assert_eq!(table.insert(network, "null"), Some("bar"));
    /// ```
    pub fn insert<N: Into<IpNet>>(&mut self, network: N, data: T) -> Option<T> {
        match network.into() {
            IpNet::V4(ipv4_network) => self.ipv4.insert(ipv4_network, data),
            IpNet::V6(ipv6_network) => self.ipv6.insert(ipv6_network, data),
        }
    }

    /// Remove a `IpNet` from table. If prefix existed, the value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ipnet_trie::IpnetTrie;
    /// use std::net::Ipv6Addr;
    /// use ipnet::Ipv6Net;
    ///
    /// let mut table = IpnetTrie::new();
    /// let network = Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    ///
    /// assert_eq!(table.insert(network, "foo"), None);
    /// // Remove network from table
    /// assert_eq!(table.remove(network), Some("foo"));
    /// // Network is removed
    /// assert_eq!(table.exact_match(network), None);
    /// ```
    pub fn remove<N: Into<IpNet>>(&mut self, network: N) -> Option<T> {
        match network.into() {
            IpNet::V4(ipv4_network) => self.ipv4.remove(&ipv4_network),
            IpNet::V6(ipv6_network) => self.ipv6.remove(&ipv6_network),
        }
    }

    /// Get pointer to value from table based on exact network match.
    /// If network is not in table, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ipnet_trie::IpnetTrie;
    /// use std::net::Ipv6Addr;
    /// use ipnet::Ipv6Net;
    ///
    /// let mut table = IpnetTrie::new();
    /// let network_a = Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// let network_b = Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 128).unwrap();
    ///
    /// assert_eq!(table.insert(network_a, "foo"), None);
    /// // Get value for network from trie
    /// assert_eq!(table.exact_match(network_a), Some(&"foo"));
    /// // Network B doesn not exist in trie
    /// assert_eq!(table.exact_match(network_b), None);
    /// ```
    pub fn exact_match<N: Into<IpNet>>(&self, network: N) -> Option<&T> {
        match network.into() {
            IpNet::V4(ipv4_network) => self.ipv4.get(&ipv4_network),
            IpNet::V6(ipv6_network) => self.ipv6.get(&ipv6_network),
        }
    }

    /// Get mutable pointer to value from table based on exact network match.
    /// If network is not in table, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ipnet_trie::IpnetTrie;
    /// use std::net::Ipv6Addr;
    /// use ipnet::Ipv6Net;
    ///
    /// let mut table = IpnetTrie::new();
    /// let network_a = Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// let network_b = Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 128).unwrap();
    ///
    /// assert_eq!(table.insert(network_a, "foo"), None);
    /// // Get value for network from trie
    /// assert_eq!(table.exact_match_mut(network_a), Some(&mut "foo"));
    /// // Network B does not exist in trie
    /// assert_eq!(table.exact_match(network_b), None);
    /// ```
    pub fn exact_match_mut<N: Into<IpNet>>(&mut self, network: N) -> Option<&mut T> {
        match network.into() {
            IpNet::V4(ipv4_network) => self.ipv4.get_mut(&ipv4_network),
            IpNet::V6(ipv6_network) => self.ipv6.get_mut(&ipv6_network),
        }
    }

    /// Find most specific IP network in table that contains given IP address. If no network in table contains
    /// given IP address, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ipnet_trie::IpnetTrie;
    /// use ipnet::{IpNet, Ipv6Net};
    /// use std::net::{IpAddr, Ipv6Addr};
    ///
    /// let mut table = IpnetTrie::new();
    /// let network = IpNet::new(IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0)), 64).unwrap();
    /// let ip_address = Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0x1);
    ///
    /// assert_eq!(table.insert(network, "foo"), None);
    /// // Get value for network from table
    /// assert_eq!(table.longest_match(&IpNet::from(ip_address.to_canonical())), Some((network, &"foo")));
    /// ```
    pub fn longest_match(&self, ipnet: &IpNet) -> Option<(IpNet, &T)> {
        match ipnet {
            IpNet::V4(net) => self
                .longest_match_ipv4(net)
                .map(|(net, data)| (IpNet::V4(*net), data)),
            IpNet::V6(net) => self
                .longest_match_ipv6(net)
                .map(|(net, data)| (IpNet::V6(*net), data)),
        }
    }

    /// Find most specific IP network in table that contains given IP address. If no network in table contains
    /// given IP address, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ipnet_trie::IpnetTrie;
    /// use ipnet::{IpNet, Ipv6Net};
    /// use std::net::{IpAddr, Ipv6Addr};
    ///
    /// let mut table = IpnetTrie::new();
    /// let network = IpNet::new(IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0)), 64).unwrap();
    /// let ip_address = Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0x1);
    ///
    /// assert_eq!(table.insert(network, "foo"), None);
    /// // Get value for network from table
    /// assert_eq!(table.longest_match_mut(&IpNet::from(ip_address.to_canonical())), Some((network, &mut "foo")));
    /// ```
    pub fn longest_match_mut(&mut self, ipnet: &IpNet) -> Option<(IpNet, &mut T)> {
        match ipnet {
            IpNet::V4(net) => self
                .longest_match_ipv4_mut(net)
                .map(|(net, data)| (IpNet::V4(*net), data)),
            IpNet::V6(net) => self
                .longest_match_ipv6_mut(net)
                .map(|(net, data)| (IpNet::V6(*net), data)),
        }
    }

    /// Specific version of `longest_match` for IPv4 address.
    #[inline]
    pub fn longest_match_ipv4(&self, net: &Ipv4Net) -> Option<(&Ipv4Net, &T)> {
        self.ipv4.get_lpm(net)
    }

    /// Specific version of `longest_match` for IPv6 address.
    #[inline]
    pub fn longest_match_ipv6(&self, net: &Ipv6Net) -> Option<(&Ipv6Net, &T)> {
        self.ipv6.get_lpm(net)
    }

    /// Specific version of `longest_match` for IPv4 address.
    #[inline]
    pub fn longest_match_ipv4_mut(&mut self, net: &Ipv4Net) -> Option<(&Ipv4Net, &mut T)> {
        self.ipv4.get_lpm_mut(net)
    }

    /// Specific version of `longest_match` for IPv6 address.
    #[inline]
    pub fn longest_match_ipv6_mut(&mut self, net: &Ipv6Net) -> Option<(&Ipv6Net, &mut T)> {
        self.ipv6.get_lpm_mut(net)
    }

    /// Find all IP networks in table that contains given IP address.
    /// Returns iterator of `IpNet` and reference to value.
    ///
    /// # Examples
    ///
    /// ```
    /// use ipnet_trie::IpnetTrie;
    /// use ipnet::{IpNet, Ipv6Net};
    /// use std::net::{IpAddr, Ipv6Addr};
    ///
    /// let mut table = IpnetTrie::new();
    /// let network = IpNet::new(IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0)), 64).unwrap();
    /// let ip_address = Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0x1);
    ///
    /// assert_eq!(table.insert(network, "foo"), None);
    /// // Get value for network from table
    /// assert_eq!(table.matches(&IpNet::from(ip_address.to_canonical())).len(), 1);
    /// ```
    pub fn matches(&self, ipnet: &IpNet) -> Vec<(IpNet, &T)> {
        match ipnet {
            IpNet::V4(net) => self
                .matches_ipv4(net)
                .into_iter()
                .map(|(net, data)| (IpNet::V4(*net), data))
                .collect(),
            IpNet::V6(net) => self
                .matches_ipv6(net)
                .into_iter()
                .map(|(net, data)| (IpNet::V6(*net), data))
                .collect(),
        }
    }

    /// Specific version of `matches` for IPv4 address.
    pub fn matches_ipv4(&self, net: &Ipv4Net) -> Vec<(&Ipv4Net, &T)> {
        match self.ipv4.get_spm(net) {
            None => vec![],
            Some((shortest, _)) => self.ipv4.children(shortest).collect(),
        }
    }

    /// Specific version of `matches` for IPv6 address.
    pub fn matches_ipv6(&self, net: &Ipv6Net) -> Vec<(&Ipv6Net, &T)> {
        match self.ipv6.get_spm(net) {
            None => vec![],
            Some((shortest, _)) => self.ipv6.children(shortest).collect(),
        }
    }

    /// Iterator for all networks in table, first are iterated IPv4 and then IPv6 networks. Order is not guaranteed.
    ///
    /// # Examples
    ///
    /// ```
    /// use ipnet_trie::IpnetTrie;
    /// use ipnet::{IpNet, Ipv4Net, Ipv6Net};
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// let mut table: IpnetTrie<&str> = IpnetTrie::new();
    /// let network_a = Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 24).unwrap();
    /// assert_eq!(table.insert(network_a, "foo"), None);
    /// let network_b = Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// assert_eq!(table.insert(network_b, "foo"), None);
    ///
    /// let mut iterator = table.iter();
    /// assert_eq!(iterator.next(), Some((IpNet::V4(network_a), &"foo")));
    /// assert_eq!(iterator.next(), Some((IpNet::V6(network_b), &"foo")));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (IpNet, &T)> {
        self.iter_ipv4()
            .map(|(network, data)| (IpNet::V4(*network), data))
            .chain(
                self.iter_ipv6()
                    .map(|(network, data)| (IpNet::V6(*network), data)),
            )
    }

    /// Mutable iterator for all networks in table, first are iterated IPv4 and then IPv6 networks. Order is not guaranteed.
    ///
    /// # Examples
    ///
    /// ```
    /// use ipnet_trie::IpnetTrie;
    /// use ipnet::{IpNet, Ipv4Net, Ipv6Net};
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// let mut table: IpnetTrie<&str> = IpnetTrie::new();
    /// let network_a = Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 24).unwrap();
    /// assert_eq!(table.insert(network_a, "foo"), None);
    /// let network_b = Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// assert_eq!(table.insert(network_b, "foo"), None);
    ///
    /// let mut iterator = table.iter_mut();
    /// for (network, value) in iterator {
    ///    *value = "bar";
    /// }
    ///
    /// assert_eq!(table.exact_match(network_a), Some(&"bar"));
    /// assert_eq!(table.exact_match(network_b), Some(&"bar"));
    /// ```
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (IpNet, &mut T)> {
        self.ipv4
            .iter_mut()
            .map(|(net, data)| (IpNet::from(*net), data))
            .chain(
                self.ipv6
                    .iter_mut()
                    .map(|(net, data)| (IpNet::from(*net), data)),
            )
    }

    /// Iterator for all IPv4 networks in table. Order is not guaranteed.
    pub fn iter_ipv4(&self) -> impl Iterator<Item = (&Ipv4Net, &T)> {
        self.ipv4.iter()
    }

    /// Iterator for all IPv6 networks in table. Order is not guaranteed.
    pub fn iter_ipv6(&self) -> impl Iterator<Item = (&Ipv6Net, &T)> {
        self.ipv6.iter()
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` such that `f(ip_network, &mut v)` returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ipnet_trie::IpnetTrie;
    /// use ipnet::{IpNet, Ipv4Net, Ipv6Net};
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// let mut table: IpnetTrie<&str> = IpnetTrie::new();
    /// let network_a = Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 24).unwrap();
    /// assert_eq!(table.insert(network_a, "foo"), None);
    /// let network_b = Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// assert_eq!(table.insert(network_b, "foo"), None);
    ///
    /// // Keep just IPv4 networks
    /// table.retain(|network, _| network.network().is_ipv4());
    ///
    /// assert_eq!(table.exact_match(network_a), Some(&"foo"));
    /// assert_eq!(table.exact_match(network_b), None);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(IpNet, &mut T) -> bool,
    {
        let mut to_delete = vec![];
        for (network, data) in self.iter_mut() {
            if !f(network, data) {
                to_delete.push(network);
            }
        }
        for network in to_delete {
            self.remove(network);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::IpnetTrie;
    use ipnet::{Ipv4Net, Ipv6Net};
    use std::net::{Ipv4Addr, Ipv6Addr};
    use std::str::FromStr;

    #[test]
    fn insert_ipv4_ipv6() {
        let mut table = IpnetTrie::new();
        table.insert(Ipv4Net::new(Ipv4Addr::new(127, 0, 0, 0), 16).unwrap(), 1);
        table.insert(
            Ipv6Net::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 128).unwrap(),
            1,
        );
    }

    #[test]
    fn exact_match_ipv4() {
        let mut table = IpnetTrie::new();
        table.insert(Ipv4Net::new(Ipv4Addr::new(127, 0, 0, 0), 16).unwrap(), 1);
        let m = table.exact_match(Ipv4Net::new(Ipv4Addr::new(127, 0, 0, 0), 16).unwrap());
        assert_eq!(m, Some(&1));
        let m = table.exact_match(Ipv4Net::new(Ipv4Addr::new(127, 0, 0, 0), 17).unwrap());
        assert_eq!(m, None);
        let m = table.exact_match(Ipv4Net::new(Ipv4Addr::new(127, 0, 0, 0), 15).unwrap());
        assert_eq!(m, None);
    }

    #[test]
    fn exact_match_ipv6() {
        let mut table = IpnetTrie::new();
        table.insert(
            Ipv6Net::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 127).unwrap(),
            1,
        );
        let m =
            table.exact_match(Ipv6Net::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 127).unwrap());
        assert_eq!(m, Some(&1));
        let m =
            table.exact_match(Ipv6Net::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 128).unwrap());
        assert_eq!(m, None);
        let m =
            table.exact_match(Ipv6Net::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 126).unwrap());
        assert_eq!(m, None);
    }

    #[test]
    fn test_ip_count() {
        let mut table = IpnetTrie::new();
        table.insert(Ipv4Net::from_str("192.0.2.129/25").unwrap(), 1);
        table.insert(Ipv4Net::from_str("192.0.2.0/24").unwrap(), 1);
        table.insert(Ipv4Net::from_str("192.0.2.0/24").unwrap(), 1);
        table.insert(Ipv4Net::from_str("192.0.2.0/24").unwrap(), 1);
        assert_eq!(table.ip_count(), (256, 0));

        table.insert(Ipv4Net::from_str("198.51.100.0/25").unwrap(), 1);
        table.insert(Ipv4Net::from_str("198.51.100.64/26").unwrap(), 1);
        assert_eq!(table.ip_count(), (384, 0));

        table.insert(Ipv4Net::from_str("198.51.100.65/26").unwrap(), 1);
        assert_eq!(table.ip_count(), (384, 0));

        table.insert(Ipv6Net::from_str("2001:DB80::/48").unwrap(), 1);
        assert_eq!(table.ip_count(), (384, 2_u128.pow(80)));
        table.insert(Ipv6Net::from_str("2001:DB80::/49").unwrap(), 1);
        assert_eq!(table.ip_count(), (384, 2_u128.pow(80)));
    }
}
