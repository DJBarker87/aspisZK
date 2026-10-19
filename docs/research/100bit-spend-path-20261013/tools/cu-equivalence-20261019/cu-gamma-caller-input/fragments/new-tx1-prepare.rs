#[inline(never)]
fn tx1_prepare<H:Digest32>(public:Public<'_>,v:&View<'_>,hash:H,obs:Observer,g:&mut [E;29])->Result<(Box<[[K;29];3]>,Box<Prepared>),Error> {
    let sem=crate::r1_semantic::verify_observed(public,v.semantic,hash,obs).map_err(|_|Error::Semantic)?;mark(obs,Phase::Semantic);
    let p=Prepared::new(&sem,v,hash,g)?;
    Ok((sem.claims,p))
}