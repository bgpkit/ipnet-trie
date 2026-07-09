# Changelog

All notable changes to this project will be documented in this file.

## v0.3.1 -- 2026-07-09

### Bug Fixes

* `ip_count` no longer panics when the trie covers a complete address space
  (e.g. `0.0.0.0/0` or `::/0`). Previously the computation overflowed, causing
  a panic in debug builds and silent wrap-around in release builds.

### Breaking Changes

* `ip_count` now returns `IpCount` (`{ ipv4: u64, ipv6: Option<u128> }`)
  instead of `(u32, u128)`. The IPv4 count is widened to `u64` to hold the
  full 2³² address space. The IPv6 count is `Option<u128>`: `None` indicates
  the entire IPv6 space (2¹²⁸ addresses) is covered, a value too large for
  `u128`.

## v0.3.0 -- 2025-03-25

### Highlight

* build `bincode` build issue
* update dependencies
    * core
        * `prefix-trie`: `0.2.5` -> `0.6.0`
        * `bincode`: `2.0.0-rc` -> `2.0.1`
        * `oneio`: `0.16` -> `0.17`
    * dev
        * `oneio`: `0.16` -> `0.17`
        * `bgpkit-parser`: `0.10` -> `0.11`

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