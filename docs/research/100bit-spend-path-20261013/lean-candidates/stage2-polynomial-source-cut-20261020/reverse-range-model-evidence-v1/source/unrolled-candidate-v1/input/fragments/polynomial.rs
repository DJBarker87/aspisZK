pub fn polynomial(bytes:&[u8],x:E)->E {
    let a=E::ZERO;
    let a=a.mul(x).add(field(bytes,6));
    let a=a.mul(x).add(field(bytes,5));
    let a=a.mul(x).add(field(bytes,4));
    let a=a.mul(x).add(field(bytes,3));
    let a=a.mul(x).add(field(bytes,2));
    let a=a.mul(x).add(field(bytes,1));
    let a=a.mul(x).add(field(bytes,0));
    a
}