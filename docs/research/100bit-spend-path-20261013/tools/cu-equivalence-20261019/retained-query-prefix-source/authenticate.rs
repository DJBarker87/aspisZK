
    #[cfg(not(feature = "private-leaf-salts"))]
    let (c1,c2,path_at) = (merkle::leaf_with_digest(hash,merkle::C1_TAG,&q[..480]),merkle::leaf_with_digest(hash,merkle::C2_TAG,&q[480..608]),608);
    #[cfg(feature = "private-leaf-salts")]
    let (c1,c2,path_at) = (
        aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,merkle::C1_TAG,&q[..480],q[608..640].try_into().unwrap()),
        aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,merkle::C2_TAG,&q[480..608],q[640..672].try_into().unwrap()),
        672,
    );
    if !merkle_path(hash,&p.roots[0],u,c1,&q[path_at..path_at+1344])||!merkle_path(hash,&p.roots[1],u,c2,&q[path_at+1344..INITIAL_QUERY_BYTES]) {return Err(Error::Merkle);}
    if p.variant.folds()==2 {
        let folded=&q[INITIAL_QUERY_BYTES..INITIAL_QUERY_BYTES+128];
        #[cfg(not(feature = "private-leaf-salts"))]
        let (leaf,path_offset)=(merkle::leaf_with_digest(hash,0x72,folded),INITIAL_QUERY_BYTES+128);
        #[cfg(feature = "private-leaf-salts")]
        let (leaf,path_offset)=(
            aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,0x72,folded,q[INITIAL_QUERY_BYTES+128..INITIAL_QUERY_BYTES+160].try_into().unwrap()),
            INITIAL_QUERY_BYTES+160,
        );
        if !merkle_path(hash,v.folded_root.unwrap(),u/4,leaf,&q[path_offset..]) {return Err(Error::Merkle);}
    }
    mark(obs,Phase::Merkle(i));
