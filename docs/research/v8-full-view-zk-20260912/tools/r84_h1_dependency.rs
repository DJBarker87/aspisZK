    // Diagnostic only. The original rank-540 gate below is retained verbatim.
    // Restrict to active, balance and final rows before raw/point observations.
    // Keep row-operation coefficients and check every original column again.
    {
        let rows:Vec<usize>=(0..215).chain(306..562).collect();
        let n=rows.len();assert_eq!(n,471);
        let mut tagged:Vec<Vec<K>>=rows.iter().enumerate().map(|(i,&r)| {
            let mut v=matrix[r].clone();v.resize(1022+n,K::ZERO);v[1022+i]=K::ONE;v
        }).collect();
        let rank=reduce(&mut tagged,1022).len();
        println!("R84_H1_SUBSPACE active_balance_final_rows=471 rank={rank} dependencies={}",n-rank);
        for (which,row) in tagged[rank..].iter().enumerate() {
            assert!(row[..1022].iter().all(|&x|x==K::ZERO));
            let coeff=&row[1022..];assert!(coeff.iter().any(|&x|x!=K::ZERO));
            for j in 0..1022 {
                assert_eq!(coeff.iter().zip(&rows).fold(K::ZERO,|s,(&c,&r)|s.add(c.mul(matrix[r][j]))),K::ZERO,"original left-kernel column {j}");
            }
            let residual=coeff.iter().zip(&rows).fold(K::ZERO,|s,(&c,&r)|s.add(c.mul(target[r])));
            let nonzero:Vec<_>=coeff.iter().zip(&rows).filter(|(&c,_)|c!=K::ZERO).map(|(&c,&r)| {
                let label=if r<214 {format!("active:{}",active[r])}else if r==214 {"balance".to_string()}else{format!("final:{}",r-306)};
                (label,[c.c0.a.0,c.c0.b.0,c.c1.a.0,c.c1.b.0])
            }).collect();
            println!("R84_H1_PUBLIC_DEPENDENCY id={which} original_columns_checked=1022 source_target_zero={} terms={nonzero:?}",residual==K::ZERO);
        }
    }
