ipnet-trie
========

IPv4 and IPv6 network fast lookup prefix trie.

[![Rust](https://github.com/bgpkit/ipnet-trie/actions/workflows/rust.yml/badge.svg)](https://github.com/bgpkit/ipnet-trie/actions/workflows/rust.yml)
[![Documentation](https://docs.rs/ipnet-trie/badge.svg)](https://docs.rs/ipnet-trie)
[![Crates.io](https://img.shields.io/crates/v/ipnet-trie.svg)](https://crates.io/crates/ipnet-trie)
[![License](https://img.shields.io/crates/l/ipnet-trie)](https://raw.githubusercontent.com/bgpkit/ipnet-trie/master/LICENSE)

## Description

This crate provides storage and retrieval of IPv4 and IPv6 network prefixes. It uses the [`ipnet`](https://docs.rs/ipnet/latest/ipnet/) crate as the IP network data structure and [`prefix-trie`](https://github.com/tiborschneider/prefix-trie) as the backend, offering fast lookup times and a small memory footprint.

## Features

- Fast prefix lookup for both IPv4 and IPv6 networks
- Efficient storage of IP prefixes and associated data
- Support for exact match and longest prefix match operations
- Ability to iterate over all stored prefixes
- Export and import functionality (with the `export` feature flag)
- Diff operation to compare two tries

## Feature flags

- `export`: Enable export of the trie to bytes or a writer, and import from bytes or a reader.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
ipnet = "2"
ipnet-trie = "0.2"
```

and then you can use it like this:

```rust
use std::net::{IpAddr, Ipv6Addr};
use ipnet::{IpNet, Ipv6Net};
use ipnet_trie::IpnetTrie;

let mut table = IpnetTrie::new();
let network = IpNet::from(Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap());
let ip_address = Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0x1);

assert_eq!(table.insert(network, "foo"), None);
// Get value for network from table
assert_eq!(table.longest_match(ip_address), Some((network, &"foo")));
```

### Insertion and Retrieval

```rust
// Insert a network
table.insert(network, value);

// Exact match
let value = table.exact_match(network);

// Longest prefix match
let (matched_network, value) = table.longest_match(&ip_address);
```

### Iteration

```rust
// Iterate over all networks
for (network, value) in table.iter() {
    // ...
}
```

### IP Count

```rust
// Get the total number of unique IPv4 and IPv6 addresses in the trie
let (ipv4_count, ipv6_count) = table.ip_count();
```

### Diff Operation

```rust
// Compare two tries
let (added, removed) = trie1.diff(&trie2);
```

### Export and Import (with `export` feature)

```rust
// Export to bytes
let bytes = table.export_to_bytes();

// Import from bytes
table.import_from_bytes(&bytes);

// Export to writer
table.export_to_writer(&mut writer)?;

// Import from reader
table.import_from_reader(&mut reader)?;
```