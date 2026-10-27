// Pure owned reference; arithmetic dictionary is instantiated with actual E.
pub trait Arithmetic {
    type E: Copy;
    fn zero() -> Self::E;
    fn mul(a: Self::E, x: Self::E) -> Self::E;
    fn add(a: Self::E, c: Self::E) -> Self::E;
    fn field(bytes: &[u8], i: usize) -> Self::E;
}
pub fn polynomial<A: Arithmetic>(bytes: &[u8], x: A::E) -> A::E {
    let a = A::add(A::mul(A::zero(),x), A::field(bytes,6));
    let a = A::add(A::mul(a,x), A::field(bytes,5));
    let a = A::add(A::mul(a,x), A::field(bytes,4));
    let a = A::add(A::mul(a,x), A::field(bytes,3));
    let a = A::add(A::mul(a,x), A::field(bytes,2));
    let a = A::add(A::mul(a,x), A::field(bytes,1));
    A::add(A::mul(a,x), A::field(bytes,0))
}
