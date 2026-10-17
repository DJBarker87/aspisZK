    pub fn new(hash:H, semantic_state:[u8;32], variant:Variant) -> Self {
        #[cfg(not(feature = "private-leaf-salts"))]
        let domain: &[u8] = b"UNPROVED:R1:COST-PROBE:P2";
        #[cfg(feature = "private-leaf-salts")]
        let domain: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:P3";
        Self { state:hash.digest(&[domain,&[variant.tag()],&semantic_state]), hash }
    }