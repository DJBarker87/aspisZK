        let mut prefixes=Vec::with_capacity(flat.len());
        let mut product=M31::ONE;
        for &value in &flat {prefixes.push(product);product=product.mul(value);}
