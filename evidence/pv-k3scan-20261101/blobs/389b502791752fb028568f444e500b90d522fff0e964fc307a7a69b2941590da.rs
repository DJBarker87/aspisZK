use aspis_core::field::M31;
// Source-local fission of the for-loop's next/copy/state operation. Returning
// the actual iterator state avoids inventing a suffix-slice representation.
pub fn iterator_step<'a>(mut iterator:core::slice::Iter<'a,M31>)->(Option<M31>,core::slice::Iter<'a,M31>) {
    let head=match iterator.next() {Some(value)=>Some(*value),None=>None};
    (head,iterator)
}
