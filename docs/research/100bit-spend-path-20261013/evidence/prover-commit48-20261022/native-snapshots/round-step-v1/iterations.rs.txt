// Generated literal native and owner iteration bodies. Loop decomposition is explicit.
fn double(x:E)->E {
    let square = x.mul(x);
    square.add(square).sub(E::ONE)
}
fn native_pair(q:&[E;1024],basis:[E;512],i:usize,mut p0:E,mut p1:E)->(E,E) {
 // Current iterator cursor under D157 chunks_exact/zip semantics.
 let (pair,n)=q[2*i..].chunks_exact(2).zip([basis[i]]).next().unwrap();
        p0 = p0.add(pair[0].mul(n));
        p1 = p1.add(pair[1].mul(n));
 (p0,p1)
}
fn owner_pair(q:[E;1024],basis:[E;512],i:usize,p0:E,p1:E)->(E,E) {
  let n=basis[i];
  let p0=p0.add(q[2*i].mul(n));
  let p1=p1.add(q[2*i+1].mul(n));
 (p0,p1)
}
fn native_fill(mut out:[E;512],width:usize,j:usize,factor:E)->[E;512] {
 assert!(j<width.min(512-width));
            out[width + j] = out[j].mul(factor);
 out
}
fn owner_fill(mut out:[E;512],width:usize,j:usize,factor:E)->[E;512] {
  out[width+j]=out[j].mul(factor);
 out
}
fn native_stage(mut width:usize,mut factor:E)->(usize,E) {
        width *= 2;
        factor = double(factor);
 (width,factor)
}
fn owner_stage(width:usize,factor:E)->(usize,E) {
 let square=factor.mul(factor);
 (width*2,square.add(square).sub(E::ONE))
}
