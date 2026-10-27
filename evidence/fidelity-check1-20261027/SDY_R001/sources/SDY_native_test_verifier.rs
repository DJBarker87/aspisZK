#[cfg(test)]
mod SDY_fidelity {
    use super::*;
    fn k(a:u32,b:u32,c:u32,d:u32)->K {K{c0:aspis_core::field::CM31{a:M31(a),b:M31(b)},c1:aspis_core::field::CM31{a:M31(c),b:M31(d)}}}
    #[test]
    fn SDY_residue_finish() {
        for (mut row,p,b,flush,expected) in [
            ([1,2,3,4],k(1,2,3,4),2,false,[3,6,9,12]),
            ([2147483648,2147483649,4294967296,7],k(0,0,0,0),0,true,[1,2,2,7]),
            ([2147483647,0,0,0],k(1,2,3,4),1,true,[1,2,3,4]),
        ] {let old=row;update_residue_row(&mut row,p,M31(b),flush);std::println!("SDY residue {:?} flush={} => {:?}",old,flush,row);assert_eq!(row,expected);}
        for (raw,expected) in [
            ([1,2,3,4],[1,2,3,4]),
            ([2147483648,2147483649,4294967296,7],[1,2,2,7]),
            ([2147483647,4294967294,0,2147483652],[0,0,0,5]),
        ] {let state=BatchedWeights{raw:alloc::vec![raw],terms:0};let mut weights=[k(99,99,99,99)];state.finish(&mut weights);let w=weights[0];let got=[w.c0.a.0,w.c0.b.0,w.c1.a.0,w.c1.b.0];std::println!("SDY finish {:?} => {:?}",raw,got);assert_eq!(got,expected);}
    }
}
