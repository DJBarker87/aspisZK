// Owned safe reference. NOT the native packed Error carrier.
// K is Copy, as native ErrorKind is; C includes every possible dynamic payload.
pub struct Custom<K, C> { pub kind: K, pub payload: C }
pub struct SimpleMessage<K, M> { pub kind: K, pub message: M }
pub enum Data<'a, K, C, M> {
    Os(i32), Custom(&'a Custom<K, C>), Simple(K),
    SimpleMessage(&'a SimpleMessage<K, M>),
}
pub enum Projection<K> { Os(i32), Stored(K) }
// The OS decoder remains a separate explicit obligation.
pub fn borrowed_kind<K: Copy, C, M>(data: Data<'_, K, C, M>) -> Projection<K> {
    match data {
        Data::Os(code) => Projection::Os(code),
        Data::Custom(c) => Projection::Stored(c.kind),
        Data::Simple(kind) => Projection::Stored(kind),
        Data::SimpleMessage(m) => Projection::Stored(m.kind),
    }
}
