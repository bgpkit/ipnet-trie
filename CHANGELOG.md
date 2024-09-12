# Changelog

All notable changes to this project will be documented in this file.

## v0.2.0 -- 2024-09-11

### Highlights

* implement `std::error::Error` for `IpnetTrieError`
    * it should work with `?` operator for `anyhow` now
* switch to `[prefix-trie](https://crates.io/crates/prefix-trie)` as the default prefix trie implementation
* improve `ip_count` implementation based on clone and sub-tree removal
* implement `diff` function to compare two ipnet-trie structs' content

### Breaking Changes

* remove `with_capacity` method
* `longest_match_ipv4` now accepts `&Ipv4Net` and returns `Option<&V>` instead of `Option<V>`
* `longest_match_ipv6` now accepts `&Ipv6Net` and returns `Option<&V>` instead of `Option<V>`
* removes `matches_mut`, `matches_ipv4_mut`, and `matches_ipv6_mut` methods