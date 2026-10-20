        let mut suffix_inverse=product.inv();
        let mut flat_inverse=Vec::with_capacity(flat.len());
        flat_inverse.resize(flat.len(),M31::ZERO);
        for i in (0..flat.len()).rev() {
            flat_inverse[i]=suffix_inverse.mul(prefixes[i]);
            suffix_inverse=suffix_inverse.mul(flat[i]);
        }
