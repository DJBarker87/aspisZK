pub fn fixed_prefix(q:&[u8])->&[u8;608] {
    let q:&[u8;608]=q[..608].try_into().unwrap();
    q
}
