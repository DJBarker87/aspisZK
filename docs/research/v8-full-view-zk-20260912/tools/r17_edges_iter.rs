// Same public carry schedule as the retained Vec routine, without allocation.
struct Edges { row:usize,bit:usize,scale:M31,done:bool }
impl Iterator for Edges {
    type Item=(usize,M31);
    fn next(&mut self)->Option<Self::Item> {
        if self.done {return None;}
        if self.row&(1<<self.bit)!=0 {
            self.row^=1<<self.bit;
            self.scale=self.scale.mul(corelib::field::M31_HALF);
            self.bit+=1;
            Some((self.row,self.scale))
        } else {
            self.done=true;
            Some((self.row|(1<<self.bit),self.scale))
        }
    }
}
fn edges(j:usize)->Edges {
    assert!(j<64);
    Edges{row:j,bit:0,scale:M31::ONE,done:false}
}
#[cfg(not(target_os="solana"))]
pub(super) fn check_edges() {
    for j in 0..64 {
        let mut actual=edges(j);
        for expected in edges_reference(j) {assert_eq!(actual.next(),Some(expected));}
        assert_eq!(actual.next(),None);assert_eq!(actual.next(),None);
    }
}
