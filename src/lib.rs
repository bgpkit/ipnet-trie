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
    /// Find the difference between two prefix tries, returning two vectors of IpNets, one for
    /// added prefixes, and one for removed prefixes.
    ///
    /// - added prefixes: all prefixes in other that are not in self
    /// - removed prefixes: all prefixes in self that are not in other
    pub fn diff(&self, other: &Self) -> (Vec<IpNet>, Vec<IpNet>) {
        let mut added = IpnetTrie::<bool>::new();
        let mut removed = IpnetTrie::<bool>::new();

        // Find added prefixes: all prefixes in self that are not in other
        // Method: build a trie using all prefixes in self, then remove all prefixes in other on the trie.
        // The remaining prefixes are the added prefixes.
        let (self_ipv4_prefixes, self_ipv6_prefixes) = self.get_aggregated_prefixes();
        let (other_ipv4_prefixes, other_ipv6_prefixes) = other.get_aggregated_prefixes();

        let mut self_ipv4_map: PrefixMap<Ipv4Net, bool> = PrefixMap::new();
        for prefix in &self_ipv4_prefixes {
            self_ipv4_map.insert(*prefix, true);
        }
        let mut other_ipv4_map: PrefixMap<Ipv4Net, bool> = PrefixMap::new();
        for prefix in &other_ipv4_prefixes {
            other_ipv4_map.insert(*prefix, true);
        }
        // check added prefixes in other
        for v4_prefix in &other_ipv4_prefixes {
            if self_ipv4_map.get_lpm(&v4_prefix).is_some() {
                // Prefix is covered by some super-prefix in self, nothing added
                continue;
            }

            // Prefix is not covered by some super-prefix in self, there might be some overlapping sub-prefixes.
            // get non-overlapping sub-prefixes
            let sub_prefixes = IpNet::aggregate(
                &self_ipv4_map
                    .children(v4_prefix)
                    .map(|(p, _)| IpNet::from(*p))
                    .collect::<Vec<IpNet>>(),
            );

            if sub_prefixes.is_empty() {
                // Self-trie does not have any sub-prefixes of the given trie
                added.insert(*v4_prefix, true);
            } else {
                // Self-trie has sub-prefixes of the given trie, in other words, the other-trie
                // added a new covering super-prefix comparing to the self-trie.

                let mut target_prefixes: Vec<IpNet> = vec![(*v4_prefix).into()];
                for sub_prefix in sub_prefixes {
                    let mut new_prefixes = vec![];
                    for target_prefix in target_prefixes {
                        // make sure none of the new prefixes overlap with the sub-prefix prefix
                        new_prefixes.extend(exclude_prefix(target_prefix, sub_prefix));
                    }

                    target_prefixes = IpNet::aggregate(&new_prefixes);
                }
                for target_prefix in target_prefixes {
                    added.insert(target_prefix, true);
                }
            }
        }
        // check deleted prefixes in other
        for v4_prefix in &self_ipv4_prefixes {
            if other_ipv4_map.get_lpm(&v4_prefix).is_some() {
                continue;
            }
            // get non-overlapping sub-prefixes
            let sub_prefixes = IpNet::aggregate(
                &other_ipv4_map
                    .children(v4_prefix)
                    .map(|(p, _)| IpNet::from(*p))
                    .collect::<Vec<IpNet>>(),
            );

            if sub_prefixes.is_empty() {
                // Self-trie does not have any sub-prefixes of the given trie
                removed.insert(*v4_prefix, true);
            } else {
                // Self-trie has sub-prefixes of the given trie, in other words, the other-trie
                // added a new covering super-prefix comparing to the self-trie.

                let mut target_prefixes: Vec<IpNet> = vec![(*v4_prefix).into()];
                for sub_prefix in sub_prefixes {
                    let mut new_prefixes = vec![];
                    for target_prefix in target_prefixes {
                        // make sure none of the new prefixes overlap with the sub-prefix prefix
                        new_prefixes.extend(exclude_prefix(target_prefix, sub_prefix));
                    }

                    target_prefixes = IpNet::aggregate(&new_prefixes);
                }
                for target_prefix in target_prefixes {
                    removed.insert(target_prefix, true);
                }
            }
        }

        let mut self_ipv6_map: PrefixMap<Ipv6Net, bool> = PrefixMap::new();
        for prefix in &self_ipv6_prefixes {
            self_ipv6_map.insert(*prefix, true);
        }
        let mut other_ipv6_map: PrefixMap<Ipv6Net, bool> = PrefixMap::new();
        for prefix in &other_ipv6_prefixes {
            other_ipv6_map.insert(*prefix, true);
        }
        // check added prefixes in other
        for v6_prefix in &other_ipv6_prefixes {
            if self_ipv6_map.get_lpm(&v6_prefix).is_some() {
                // Prefix is covered by some super-prefix in self, nothing added
                continue;
            }

            // Prefix is not covered by some super-prefix in self, there might be some overlapping sub-prefixes.
            // get non-overlapping sub-prefixes
            let sub_prefixes = IpNet::aggregate(
                &self_ipv6_map
                    .children(v6_prefix)
                    .map(|(p, _)| IpNet::from(*p))
                    .collect::<Vec<IpNet>>(),
            );

            if sub_prefixes.is_empty() {
                // Self-trie does not have any sub-prefixes of the given trie
                added.insert(*v6_prefix, true);
            } else {
                // Self-trie has sub-prefixes of the given trie, in other words, the other-trie
                // added a new covering super-prefix comparing to the self-trie.

                let mut target_prefixes: Vec<IpNet> = vec![(*v6_prefix).into()];
                for sub_prefix in sub_prefixes {
                    let mut new_prefixes = vec![];
                    for target_prefix in target_prefixes {
                        // make sure none of the new prefixes overlap with the sub-prefix prefix
                        new_prefixes.extend(exclude_prefix(target_prefix, sub_prefix));
                    }

                    target_prefixes = IpNet::aggregate(&new_prefixes);
                }
                for target_prefix in target_prefixes {
                    added.insert(target_prefix, true);
                }
            }
        }
        // check deleted prefixes in other
        for v6_prefix in &self_ipv6_prefixes {
            if other_ipv6_map.get_lpm(&v6_prefix).is_some() {
                continue;
            }
            // get non-overlapping sub-prefixes
            let sub_prefixes = IpNet::aggregate(
                &other_ipv6_map
                    .children(v6_prefix)
                    .map(|(p, _)| IpNet::from(*p))
                    .collect::<Vec<IpNet>>(),
            );

            if sub_prefixes.is_empty() {
                // Self-trie does not have any sub-prefixes of the given trie
                removed.insert(*v6_prefix, true);
            } else {
                // Self-trie has sub-prefixes of the given trie, in other words, the other-trie
                // added a new covering super-prefix comparing to the self-trie.

                let mut target_prefixes: Vec<IpNet> = vec![(*v6_prefix).into()];
                for sub_prefix in sub_prefixes {
                    let mut new_prefixes = vec![];
                    for target_prefix in target_prefixes {
                        // make sure none of the new prefixes overlap with the sub-prefix prefix
                        new_prefixes.extend(exclude_prefix(target_prefix, sub_prefix));
                    }

                    target_prefixes = IpNet::aggregate(&new_prefixes);
                }
                for target_prefix in target_prefixes {
                    removed.insert(target_prefix, true);
                }
            }
        }

        (
            added.iter().map(|(p, _)| p).collect(),
            removed.iter().map(|(p, _)| p).collect(),
        )
    }
}

/// Splits a source IP network into multiple IP networks based on a target IP network.
///
/// It makes sure the returning IP networks are non-overlapping and does not include the target prefix.
///
/// # Arguments
///
/// * `source` - The source IP network to split.
/// * `target` - The target IP network used for splitting.
///
/// # Returns
///
/// A vector containing the split IP networks.
/// ```
/// use std::net::{IpAddr, Ipv4Addr};
/// use ipnet::{IpNet, Ipv4Net};
/// use ipnet_trie::exclude_prefix;
///
/// let source: IpNet = IpNet::V4(Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 22).unwrap());
/// let target: IpNet = IpNet::V4(Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 24).unwrap());
/// let split_networks = exclude_prefix(source, target);
/// assert_eq!(split_networks.len(), 2);
///
/// let source: IpNet = IpNet::V4(Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 24).unwrap());
/// let target: IpNet = IpNet::V4(Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 24).unwrap());
/// let split_networks = exclude_prefix(source, target);
/// assert_eq!(split_networks.len(), 0);
///
/// let source: IpNet = IpNet::V4(Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 23).unwrap());
/// let target: IpNet = IpNet::V4(Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 24).unwrap());
/// let split_networks = exclude_prefix(source, target);
/// assert_eq!(split_networks.len(), 1);
/// assert_ne!(split_networks[0], source);
///
/// let source: IpNet = IpNet::V4(Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 24).unwrap());
/// let target: IpNet = IpNet::V4(Ipv4Net::new(Ipv4Addr::new(192, 168, 0, 0), 23).unwrap());
/// let split_networks = exclude_prefix(source, target);
/// assert_eq!(split_networks[0], source);
/// assert_eq!(split_networks.len(), 1);
/// ```
pub fn exclude_prefix(source: IpNet, target: IpNet) -> Vec<IpNet> {
    let new_prefixes = match source.contains(&target) {
        true => {
            // target_prefix is covered by sub_prefix, split it!
            source
                .subnets(target.prefix_len())
                .unwrap()
                .into_iter()
                .filter_map(|p| match p == target {
                    true => None,
                    false => Some(p),
                })
                .collect()
        }
        false => {
            // target_prefix is not covered by sub_prefix, keep it as is
            vec![source]
        }
    };

    IpNet::aggregate(&new_prefixes)
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
        let (root_ipv4_prefixes, root_ipv6_prefixes) = self.get_aggregated_prefixes();

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

    /// Retrieves the aggregated prefixes for both IPv4 and IPv6 from the given data.
    ///
    /// # Returns
    ///
    /// A tuple containing two vectors. The first vector contains the aggregated IPv4 prefixes,
    /// and the second vector contains the aggregated IPv6 prefixes.
    pub fn get_aggregated_prefixes(&self) -> (Vec<Ipv4Net>, Vec<Ipv6Net>) {
        // get a Vector of all prefixes for IPv4 and IPv6
        let mut all_prefixes = self
            .ipv4
            .iter()
            .map(|(net, _data)| IpNet::from(*net))
            .collect::<Vec<IpNet>>();
        all_prefixes.extend(self.ipv6.iter().map(|(net, _data)| IpNet::from(*net)));

        // get the aggregated prefixes
        let aggregated_prefixes = IpNet::aggregate(&all_prefixes);

        // split aggregated_prefixes into IPv4 and IPv6 prefixes
        let mut ipv4_prefixes = Vec::new();
        let mut ipv6_prefixes = Vec::new();
        for prefix in aggregated_prefixes {
            match prefix {
                IpNet::V4(net) => ipv4_prefixes.push(net),
                IpNet::V6(net) => ipv6_prefixes.push(net),
            }
        }
        (ipv4_prefixes, ipv6_prefixes)
    }
}

#[cfg(test)]
mod tests {
    use crate::IpnetTrie;
    use ipnet::{IpNet, Ipv4Net, Ipv6Net};
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

    #[test]
    fn test_comparison() {
        let mut trie_1 = IpnetTrie::new();
        trie_1.insert(Ipv4Net::from_str("192.168.0.0/23").unwrap(), 1);
        trie_1.insert(Ipv4Net::from_str("192.168.2.0/24").unwrap(), 1);

        let mut trie_2 = IpnetTrie::new();
        trie_2.insert(Ipv4Net::from_str("192.168.2.0/24").unwrap(), 1);

        let (_added, removed) = trie_1.diff(&trie_2);
        assert_eq!(removed.len(), 1);
        assert_eq!(
            removed[0],
            IpNet::V4(Ipv4Net::from_str("192.168.0.0/23").unwrap())
        );

        trie_2.insert(Ipv4Net::from_str("192.168.0.0/24").unwrap(), 1);
        let (_added, removed) = trie_1.diff(&trie_2);
        assert_eq!(removed.len(), 1);
        assert_eq!(
            removed[0],
            IpNet::from(Ipv4Net::from_str("192.168.1.0/24").unwrap())
        );

        trie_2.insert(Ipv4Net::from_str("192.168.3.0/24").unwrap(), 1);
        let (added, removed) = trie_1.diff(&trie_2);
        assert_eq!(removed.len(), 1);
        assert_eq!(
            removed[0],
            IpNet::from(Ipv4Net::from_str("192.168.1.0/24").unwrap())
        );
        assert_eq!(added.len(), 1);
        assert_eq!(
            added[0],
            IpNet::from(Ipv4Net::from_str("192.168.3.0/24").unwrap())
        );

        trie_2.insert(Ipv6Net::from_str("2001:DB80::/48").unwrap(), 1);
        let (added, removed) = trie_1.diff(&trie_2);
        assert_eq!(removed.len(), 1);
        assert_eq!(
            removed[0],
            IpNet::from(Ipv4Net::from_str("192.168.1.0/24").unwrap())
        );
        assert_eq!(added.len(), 2);
        assert_eq!(
            added[0],
            IpNet::from(Ipv4Net::from_str("192.168.3.0/24").unwrap())
        );
        assert_eq!(
            added[1],
            IpNet::from(Ipv6Net::from_str("2001:DB80::/48").unwrap())
        );
    }
}
