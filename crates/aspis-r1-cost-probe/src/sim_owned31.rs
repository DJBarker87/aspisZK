//! Proof-only publication owners. The native simulator remains authoritative.
//! Ordered snapshots consume `pop_first`, so no BTreeMap iterator trait is
//! passed to extraction. Standard map laws remain TrustedStd obligations.
use super::*;

pub fn entries<K:Ord,V>(mut map:BTreeMap<K,V>)->Vec<(K,V)> {
    let mut output=Vec::new();
    while let Some(entry)=map.pop_first() {output.push(entry);}
    output
}

/// Returns the replaced table even on conflict. The outer caller discards it
/// on Err, exactly as the native publication loop does.
pub fn merge_step(mut table:Table,address:Vec<u8>,answer:[u8;32])->(Table,bool) {
    let bad=match table.insert(address,answer) {Some(old)=>old!=answer,None=>false};
    (table,bad)
}
pub fn merge(mut table:Table,transcript:Vec<(Vec<u8>,[u8;32])>)->Result<Table,Error> {
    let mut i=0;
    while i<transcript.len() {
        let (address,answer)=transcript[i].clone();
        let (next,bad)=merge_step(table,address,answer);table=next;
        if bad {return Err(Error::Transcript);}
        i+=1;
    }
    Ok(table)
}

pub fn append_nodes(mut out:Vec<u8>,nodes:Vec<u8>,cap:usize)->Result<Vec<u8>,Error> {
    if nodes.len()>cap {return Err(Error::Parse);}
    out.extend_from_slice(&nodes);out.resize(out.len()+cap-nodes.len(),0);
    Ok(out)
}

pub fn sim_e_ablated(public:Public<'_>,seed:[u8;32],ablation:Ablation)->Result<Simulated,Error> {
    let variant=Variant::S2;
    let start=std::time::Instant::now();
    let mut times=SimTimes::default();
    let public_bytes=public.public_bytes().map_err(|_|Error::Semantic)?;
    for k in 0..ATTEMPT_CAP {
        // 1–2. Coins and the draw.
        let t=std::time::Instant::now();
        let mut transcript_coins=Coins::new(seed,k as u32,0);
        let mut root_coins=Coins::new(seed,k as u32,1);
        let mut commit_coins=Coins::new(seed,k as u32,2);
        let mut tape_coins=Coins::new(seed,k as u32,3);
        let answers:Vec<[u8;32]>=(0..115).map(|_|transcript_coins.coin()).collect();
        let roots=[root_coins.coin(),root_coins.coin(),root_coins.coin()];
        let state=RefCell::new(CoinState{coins:answers,next:0,record:None,collision:false});
        let drawn=walk(CoinOracle(&state),&public_bytes,&Records::placeholder()?,variant);
        times.draw+=t.elapsed().as_secs_f64();
        let drawn=match drawn {Ok(d) if state.borrow().next==115 && d.z[0]!=d.z[1]=>d,_=>continue};
        // 3. P_R1 on the drawn challenges.
        let t=std::time::Instant::now();
        let check=R1PublicChallenges{alpha:core::array::from_fn(|i|drawn.sem[15+i]),z:[[drawn.z[0].x,drawn.z[0].y],[drawn.z[1].x,drawn.z[1].y]],
            gamma:drawn.gamma,kappa:drawn.kappa,alpha0:drawn.alpha0,alpha1:drawn.alpha1,queries:drawn.queries.to_vec()};
        let (accepted,_)=aspis_z4b_probe::p_r1_check(&check);
        times.p_r1+=t.elapsed().as_secs_f64();
        if !accepted {continue;}
        // 4. The tape.
        let t=std::time::Instant::now();
        let tau=tape(&public_bytes,variant,&mut tape_coins)?;
        times.tape=t.elapsed().as_secs_f64();
        // 5. The view.
        let t=std::time::Instant::now();
        let (semantic_records,columns)=semantic(public,&tau,&drawn,&roots[1],variant,ablation)?;
        times.semantic=t.elapsed().as_secs_f64();
        let t=std::time::Instant::now();
        let mut view=opening(&columns,&tau,&drawn,variant)?;
        view.semantic=semantic_records;
        times.opening=t.elapsed().as_secs_f64();
        // 6. Commitment programming and serialisation.
        let t=std::time::Instant::now();
        let table=RefCell::new((Table::new(),false));
        let coeffs:Vec<Message<E>>=view.messages.iter().map(|m|variant.coefficients(m)).collect();
        let base:Vec<[M31;1024]>=(0..26).map(|l|coeffs[l].map(|x|M31(x.to_limbs()[0]))).collect();
        let ext:Vec<[K;1024]>=(26..29).map(|l|coeffs[l].map(|x|x.c0())).collect();
        let mut opened:BTreeMap<usize,([[E;29];4],Vec<u8>,Vec<u8>)>=BTreeMap::new();
        for &u in &drawn.queries {
            let u=u as usize;
            let mut values=[[E::ZERO;29];4];
            for l in 0..26 { let v=encode_at(&base[l],u); for s in 0..4 {values[s][l]=E::from_m31(v[s]);} }
            for l in 26..29 { let v=encode_at(&ext[l-26],u); for s in 0..4 {values[s][l]=E::from_qm31(v[s]);} }
            let mut c1v=Vec::with_capacity(480);let mut c2v=Vec::with_capacity(128);
            for s in 0..4 { for l in (0..26).chain(core::iter::once(28)) {c1v.extend_from_slice(&values[s][l].to_le_bytes()[..if l<26 {4} else {16}]);} }
            for s in 0..4 { for l in 26..28 {c2v.extend_from_slice(&values[s][l].to_le_bytes()[..16]);} }
            opened.insert(u,(values,c1v,c2v));
        }
        let mut folded:BTreeMap<usize,Vec<u8>>=BTreeMap::new();
        for &u in &drawn.queries { let v=u as usize/4; folded.entry(v).or_insert_with(||encoded((4*v..4*v+4).map(|i|eval_at(&view.q1,i)))); }
        let mut leaves1=BTreeMap::new();let mut leaves2=BTreeMap::new();let mut leavesf=BTreeMap::new();
        let opened_entries=entries(opened.clone());
        let mut i=0;
        while i<opened_entries.len() {
            let (u,(_,c1v,c2v))=opened_entries[i].clone();
            leaves1.insert(u,(c1v,commit_coins.coin()));
            leaves2.insert(u,(c2v,commit_coins.coin()));i+=1;
        }
        let folded_entries=entries(folded.clone());
        let mut i=0;
        while i<folded_entries.len() {
            let (v,fv)=folded_entries[i].clone();
            leavesf.insert(v,(fv,commit_coins.coin()));i+=1;
        }
        let (p1,r1)=program_tree(&table,&mut commit_coins,merkle::C1_TAG,&leaves1,roots[0])?;
        let (p2,r2)=program_tree(&table,&mut commit_coins,merkle::C2_TAG,&leaves2,roots[1])?;
        let (pf,rf)=program_tree(&table,&mut commit_coins,0x72,&leavesf,roots[2])?;
        let records=Records{c1_root:roots[0],semantic:view.semantic.clone(),y1:view.y1.clone(),inactive:view.inactive,c0:view.c0.clone(),folded_root:roots[2],c1:view.c1.clone(),fin:view.fin.clone()};
        let mut out=Vec::with_capacity(compact::PROOF_BYTES);
        out.extend_from_slice(compact::MAGIC);out.extend_from_slice(&[variant.tag(),0,0,0,0,0,0,0]);
        let mut logical=records.c1_root.to_vec();
        for r in &records.semantic {logical.extend_from_slice(r);}
        compact::compact_semantic(&logical,&mut out).map_err(|_|Error::Semantic)?;
        compact::compact_values(&records.y1,&mut out).map_err(|_|Error::Semantic)?;
        out.extend_from_slice(&records.inactive);out.extend_from_slice(&records.c0);
        out.extend_from_slice(&records.folded_root);out.extend_from_slice(&records.c1);out.extend_from_slice(&records.fin);
        for &u in &drawn.queries {
            let u=u as usize;let (_,c1v,c2v)=&opened[&u];
            out.extend_from_slice(c1v);out.extend_from_slice(c2v);
            out.extend_from_slice(&leaves1[&u].1);out.extend_from_slice(&leaves2[&u].1);
            out.extend_from_slice(&folded[&(u/4)]);out.extend_from_slice(&leavesf[&(u/4)].1);
        }
        if out.len()!=compact::OFF_NODES {return Err(Error::Parse);}
        for (batch,range) in [(0,0..compact::SPLIT),(1,compact::SPLIT..compact::QUERIES)] {
            let mut tree=0;
            while tree<3 {
                let programmed=if tree==0 {&p1} else if tree==1 {&p2} else {&pf};
                let mut indices:Vec<u32>=drawn.queries[range.clone()].iter().map(|&u|if tree==2 {u/4} else {u}).collect();
                indices.sort();indices.dedup();
                let nodes=programmed.multiproof(&indices)?;
                let cap=32*compact::SLOT_NODES[3*batch+tree];
                if nodes.len()>cap {return Err(Error::Parse);}
                out=append_nodes(out,nodes,cap)?;tree+=1;
            }
        }
        if out.len()!=compact::PROOF_BYTES {return Err(Error::Parse);}
        // VerLog, transcript part: the same answers at the view's addresses.
        let state=RefCell::new(CoinState{coins:state.into_inner().coins,next:0,record:Some(Table::new()),collision:false});
        let again=walk(CoinOracle(&state),&public_bytes,&records,variant)?;
        let state=state.into_inner();
        if again!=drawn||state.next!=115||state.collision {return Err(Error::Transcript);}
        let (mut table,collision)=table.into_inner();
        if collision {return Err(Error::Merkle);}
        let transcript=state.record.unwrap();
        let transcript_reads=transcript.len();
        table=merge(table,entries(transcript))?;
        times.program=t.elapsed().as_secs_f64();
        times.total=start.elapsed().as_secs_f64();
        return Ok(Simulated{proof:out,table,attempts:k+1,transcript_reads,commitment_reads:r1+r2+rf,times});
    }
    Err(Error::AttemptsExhausted)
}

