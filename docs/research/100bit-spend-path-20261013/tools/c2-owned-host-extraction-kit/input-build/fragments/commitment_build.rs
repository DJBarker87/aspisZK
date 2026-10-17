    fn build(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        private_salts: Option<PrivateSalts>,
    ) -> Result<Self, Error> {
        if messages.len() != LANES {
            return Err(Error::WrongLength);
        }
        if private_salts.as_ref().is_some_and(|salts| salts.len() != FIBRE_COUNT) {
            return Err(Error::WrongLength);
        }
        let indices: &[usize] = match time {
            CommitmentTime::C1 => &[
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 25, 28,
            ],
            CommitmentTime::C2 => &[26, 27],
        };
        let mut lanes = filled(indices.len(), 0)?;
        lanes.copy_from_slice(indices);
        let mut words = Vec::new();
        words
            .try_reserve_exact(lanes.len())
            .map_err(|_| Error::Allocation)?;
        let mut saved = Vec::new();
        saved
            .try_reserve_exact(lanes.len())
            .map_err(|_| Error::Allocation)?;
        for &l in &lanes {
            if messages[l].iter().any(|x| {
                x.to_limbs()[if l < 26 { 1 } else { 4 }..]
                    .iter()
                    .any(|&d| d != 0)
            }) {
                return Err(Error::WrongField);
            }
            // API inputs and retained matching data are semantic rows; only
            // Enc consumes coefficients. W_l = Enc(t_l ∘ π⁻¹), D13.
            let coefficients = variant.coefficients(&messages[l]);
            words.push(if l < 26 {
                Word::Base(domain.encode(&coefficients.map(|x| M31(x.to_limbs()[0])))?)
            } else {
                Word::Secure(domain.encode(&coefficients.map(|x| x.c0()))?)
            });
            saved.push(messages[l]);
        }
        let mut leaves = filled(FIBRE_COUNT, [0; 32])?;
        for (u, digest) in leaves.iter_mut().enumerate() {
            let mut bytes = [0u8; 480];
            let mut at = 0;
            for s in 0..4 {
                for (j, &l) in lanes.iter().enumerate() {
                    let b = words[j].value(4 * u + s).to_le_bytes();
                    let width = if l < 26 { 4 } else { 16 };
                    bytes[at..at + width].copy_from_slice(&b[..width]);
                    at += width;
                }
            }
            let tag = if time == CommitmentTime::C1 { merkle::C1_TAG } else { merkle::C2_TAG };
            *digest = if let Some(salts) = private_salts.as_ref() {
                aspis_core::state_only_private_merkle::private_leaf_hash(hash, tag, &bytes[..at], salts.get(u))
            } else {
                merkle::leaf(hash, tag, &bytes[..at])
            };
        }
        Ok(Self {
            time,
            lanes,
            messages: saved,
            words,
            tree: Tree::new(hash, leaves)?,
            private_salts,
        })
    }