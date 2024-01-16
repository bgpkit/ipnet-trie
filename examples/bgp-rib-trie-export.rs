use ipnet::IpNet;
use ipnet_trie::IpnetTrie;
use std::collections::HashSet;
use std::str::FromStr;

fn main() {
    println!("downloading RIB from RouteViews NWAX collector");
    let mut trie = IpnetTrie::<HashSet<u32>>::new();
    for elem in bgpkit_parser::BgpkitParser::new(
        "http://archive.routeviews.org/route-views.nwax/bgpdata/2024.01/RIBS/rib.20240101.0000.bz2",
    )
    .unwrap()
    {
        let prefix = elem.prefix.prefix;
        let origin_asn = match elem.get_origin_asn_opt() {
            Some(asn) => asn,
            None => continue,
        };
        if let Some(value) = trie.exact_match_mut(prefix) {
            value.insert(origin_asn);
        } else {
            let mut value = HashSet::new();
            value.insert(origin_asn);
            trie.insert(prefix, value);
        }
    }

    println!("exporting RIB trie to bgp-rib-trie.bin.gz");
    let mut writer = oneio::get_writer("bgp-rib-trie.bin.gz").unwrap();
    trie.export_to_writer(&mut writer).unwrap();
    drop(writer);

    println!("importing RIB trie from bgp-rib-trie.bin.gz");
    let mut new_trie = IpnetTrie::<HashSet<u32>>::new();
    let mut reader = oneio::get_reader("bgp-rib-trie.bin.gz").unwrap();
    new_trie.import_from_reader(&mut reader).unwrap();
    assert_eq!(trie.iter().count(), new_trie.iter().count());
    let quad_one_origins = trie
        .exact_match(IpNet::from_str("1.1.1.0/24").unwrap())
        .unwrap();
    assert_eq!(quad_one_origins.len(), 1);
    assert!(quad_one_origins.contains(&13335));
}
