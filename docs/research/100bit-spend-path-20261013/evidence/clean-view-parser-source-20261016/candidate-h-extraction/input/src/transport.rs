#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Variant { S1, S2, D }
impl Variant {
    pub fn from_tag(tag:u8) -> Option<Self> { match tag {1=>Some(Self::S1),2=>Some(Self::S2),3=>Some(Self::D),_=>None} }
    pub fn folds(self) -> usize { if self == Self::S1 { 1 } else { 2 } }
    pub fn final_len(self) -> usize { 1024 >> (2*self.folds()) }
}
