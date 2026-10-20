fn for_range(queries:&[u32;22],start:usize,end:usize)->Result<Self,Error> {
        if start>end||end>queries.len(){return Err(Error::Query);}
        let mut denominators=Vec::with_capacity(end-start);
        let mut flat=Vec::with_capacity((end-start)*5);
        for &query in &queries[start..end] {
            let u=query as usize;
            let fibre=domain::FibreIndex::new(u).map_err(|_|Error::Query)?;
            let point=crate::fast_domain::fibre_point(fibre);
            let line_x=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4).map_err(|_|Error::Query)?);
            let line_y=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4+3).map_err(|_|Error::Query)?);
            let line_z=line_x.mul(line_x).double().sub(M31::ONE);
            let values=[point.x,point.y,line_x,line_y,line_z];
            if values.iter().any(|x|*x==M31::ZERO){return Err(Error::Query);}
            flat.extend_from_slice(&values);
            denominators.push(values);
        }
        if flat.is_empty(){return Ok(Self{start,inverses:Vec::new()});}
        // Standard prefix-product/backward batch inversion. The only `inv`
        // in this routine is applied to the product of all nonzero entries.
        let mut prefixes=Vec::with_capacity(flat.len());
        let mut product=M31::ONE;
        for &value in &flat {prefixes.push(product);product=product.mul(value);}
        let mut suffix_inverse=product.inv();
        let mut flat_inverse=Vec::with_capacity(flat.len());
        flat_inverse.resize(flat.len(),M31::ZERO);
        for i in (0..flat.len()).rev() {
            flat_inverse[i]=suffix_inverse.mul(prefixes[i]);
            suffix_inverse=suffix_inverse.mul(flat[i]);
        }
        let inverses=(0..denominators.len()).map(|i|core::array::from_fn(|j|flat_inverse[5*i+j])).collect();
        Ok(Self{start,inverses})
    }