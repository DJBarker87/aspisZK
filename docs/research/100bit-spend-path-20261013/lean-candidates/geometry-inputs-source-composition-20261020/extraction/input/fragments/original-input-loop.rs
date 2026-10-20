        if start>end||end>queries.len(){return Err(Error::Query);}
        let mut line_z_values=Vec::with_capacity(end-start);
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
            line_z_values.push(line_z);
        }
