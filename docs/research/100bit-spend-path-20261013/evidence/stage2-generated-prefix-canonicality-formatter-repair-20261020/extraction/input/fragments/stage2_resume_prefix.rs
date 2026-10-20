
#[inline(never)]
pub fn resume_read_prefix(bytes:&[u8])->Result<([u8;32],[[u8;32];2],E,E,[E;2],K,usize),Error> {
let mut r=Reader{bytes,at:80};let state=r.raw();let roots=[r.raw(),r.raw()];
    let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];let rho=r.k()?;
    Ok((state,roots,gamma,kappa,alpha,rho,r.at))
}
