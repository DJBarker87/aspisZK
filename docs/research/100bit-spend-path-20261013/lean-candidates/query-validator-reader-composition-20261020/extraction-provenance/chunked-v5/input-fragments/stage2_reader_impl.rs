impl<'a> Reader<'a>{
    fn raw<const N:usize>(&mut self)->[u8;N] {let b=self.bytes[self.at..self.at+N].try_into().unwrap();self.at+=N;b}
    fn e(&mut self)->Result<E,Error>{E::from_le_bytes(&self.raw::<32>()).ok_or(Error::Checkpoint)}
    fn k(&mut self)->Result<K,Error>{K::from_le_bytes(&self.raw::<16>()).ok_or(Error::Checkpoint)}
}