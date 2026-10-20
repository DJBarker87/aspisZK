
    let i = a.next;
    let u = p.queries[i] as usize;
    let q = opening(proof, i);
    let dots = crate::fast_dots::four_dots(q, g);