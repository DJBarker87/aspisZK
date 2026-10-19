pub struct Enumerate<I> {
    iter: I,
    count: usize,
}
impl<'a,T> Iterator for Enumerate<core::slice::IterMut<'a,T>> {
type Item = (usize, &'a mut T);
fn next(&mut self) -> Option<Self::Item> {
        let a = self.iter.next()?;
        let i = self.count;
        self.count += 1;
        Some((i, a))
    }
}
