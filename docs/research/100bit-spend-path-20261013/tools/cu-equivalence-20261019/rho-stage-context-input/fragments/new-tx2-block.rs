    let mut pending=BatchedWeights::new(&a.weights)?;
    while a.next<22 {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry,Some(&mut pending))?;}
    pending.finish(&mut a.weights);
