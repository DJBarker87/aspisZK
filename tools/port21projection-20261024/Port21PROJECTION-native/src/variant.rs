#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Variant { S1, S2, D }
pub const TAU: [usize; 5] = [3, 4, 2, 0, 1];
impl Variant {
    pub fn tag(self) -> u8 { match self { Self::S1=>1,Self::S2=>2,Self::D=>3 } }
    pub fn from_tag(tag:u8) -> Option<Self> { match tag {1=>Some(Self::S1),2=>Some(Self::S2),3=>Some(Self::D),_=>None} }
    pub fn folds(self) -> usize { if self == Self::S1 { 1 } else { 2 } }
    pub fn final_len(self) -> usize { 1024 >> (2*self.folds()) }
}
