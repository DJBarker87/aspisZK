fn native_folded(drawn:&Drawn,view:&View)->BTreeMap<usize,Vec<u8>> {let mut folded=BTreeMap::new();
        for &u in &drawn.queries { let v=u as usize/4; folded.entry(v).or_insert_with(||encoded((4*v..4*v+4).map(|i|eval_at(&view.q1,i)))); }
folded}
fn native_leaves(opened:&BTreeMap<usize,(u8,Vec<u8>,Vec<u8>)>,folded:&BTreeMap<usize,Vec<u8>>,commit_coins:&mut Coins)->(BTreeMap<usize,(Vec<u8>,[u8;32])>,BTreeMap<usize,(Vec<u8>,[u8;32])>,BTreeMap<usize,(Vec<u8>,[u8;32])>) {let opened=opened.clone();let folded=folded.clone();let mut leaves1=BTreeMap::new();let mut leaves2=BTreeMap::new();let mut leavesf=BTreeMap::new();
        for (&u,(_,c1v,c2v)) in &opened { leaves1.insert(u,(c1v.clone(),commit_coins.coin())); leaves2.insert(u,(c2v.clone(),commit_coins.coin())); }
        for (&v,fv) in &folded { leavesf.insert(v,(fv.clone(),commit_coins.coin())); }
(leaves1,leaves2,leavesf)}
fn native_publish(drawn:&Drawn,opened:&BTreeMap<usize,(u8,Vec<u8>,Vec<u8>)>,leaves1:&BTreeMap<usize,(Vec<u8>,[u8;32])>,leaves2:&BTreeMap<usize,(Vec<u8>,[u8;32])>,folded:&BTreeMap<usize,Vec<u8>>,leavesf:&BTreeMap<usize,(Vec<u8>,[u8;32])>)->Vec<u8> {let mut out=Vec::new();
        for &u in &drawn.queries {
            let u=u as usize;let (_,c1v,c2v)=&opened[&u];
            out.extend_from_slice(c1v);out.extend_from_slice(c2v);
            out.extend_from_slice(&leaves1[&u].1);out.extend_from_slice(&leaves2[&u].1);
            out.extend_from_slice(&folded[&(u/4)]);out.extend_from_slice(&leavesf[&(u/4)].1);
        }
out}
fn native_merge(mut table:Table,transcript:Table)->Result<Table,Error> {
        for (a,v) in transcript { if let Some(p)=table.insert(a,v) { if p!=v {return Err(Error::Transcript);} } }
Ok(table)}
