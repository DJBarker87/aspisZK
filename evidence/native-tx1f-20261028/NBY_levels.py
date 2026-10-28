import NBY_generate as g
g.text='''use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]struct NoHash<'a>(&'a Cell<usize>);
impl Digest32 for NoHash<'_>{fn digest(&self,_:&[&[u8]])->[u8;32]{self.0.set(self.0.get()+1);panic!("unreached digest")}}
'''
# Whole-function early rejections have no iteration and no hash.
common='''let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let k:usize=kani::any();let c:usize=kani::any();let prior:usize=kani::any();kani::assume(k<16&&c<32&&prior<1000);let old_i=idx[k];let old_v=val[k][c];let calls=Cell::new(prior);'''
g.pair('verify_invalid_n_frame',common+'''let n:usize=kani::any();kani::assume(n==0||n>16);let nodes:[u8;64]=kani::any();let out=verify_in_place(NoHash(&calls),Arity::Two,&root,&mut idx,&mut val,n,&nodes);''','!out&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior')
g.pair('verify_first_pair_rejection_frame',common+'''let n:usize=kani::any();kani::assume(n>=2&&n<=16&&idx[0]>=idx[1]);let nodes:[u8;64]=kani::any();let out=verify_in_place(NoHash(&calls),Arity::Two,&root,&mut idx,&mut val,n,&nodes);''','!out&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior')
# Final source Boolean continuation from the SAME arbitrary scratch and cursor.
g.pair('verify_return_frame',common+'''let n:usize=kani::any();let at:usize=kani::any();let len:usize=kani::any();let leaf_ok=n==1&&index_at(&idx,0)==0&&root_matches(&val,&root)&&at==len;let result:Result<(),u8>=if !leaf_ok{Err(1)}else{Ok(())};''','result.is_ok()==(n==1&&idx[0]==0&&val[0]==root&&at==len)&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior')
# Outer source iteration consumes current level's n=w before resetting counters.
g.pair('verify_level_carrier_transition',common+'''let depth:u32=kani::any();let w:usize=kani::any();let mut n:usize=kani::any();let at:usize=kani::any();kani::assume(depth<18&&n>0&&n<=16&&w>0&&w<=n&&at<=5504);n=w;let mut levels=depth+1..Arity::Two.levels();let next=levels.next();let i=0usize;let next_w=0usize;''','n==w&&n<=16&&i<=n&&next_w<=i&&at<=5504&&next==if depth<17{Some(depth+1)}else{None}&&idx[k]==old_i&&val[k][c]==old_v&&calls.get()==prior')
if __name__=='__main__':g.publish('NBY_levels','multiproof.rs',65)
