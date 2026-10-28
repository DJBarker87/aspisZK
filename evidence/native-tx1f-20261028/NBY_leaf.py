import NBY_generate as g
g.text='''use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]struct Port<'a>{q:&'a[u8;832],tree:usize,c:usize,reply:&'a[u8;32],calls:&'a Cell<usize>}
impl Digest32 for Port<'_>{fn digest(&self,p:&[&[u8]])->[u8;32]{let (tag,start,len,salt)=if self.tree==0{(0x71,0,480,608)}else if self.tree==1{(0xf1,480,128,640)}else{(0x72,672,128,800)};assert_eq!(p.len(),3);assert_eq!(p[0],&[0x10,tag]);assert_eq!(p[1].len(),len);assert_eq!(p[1].as_ptr(),self.q[start..].as_ptr());assert_eq!(p[2].len(),32);assert_eq!(p[2][self.c],self.q[salt+self.c]);self.calls.set(self.calls.get()+1);*self.reply}}
'''
for tree in range(3):
 for effect in ['inside','outside']:
  body=f'''let q:[u8;832]=kani::any();let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let reply:[u8;32]=kani::any();let index:u32=kani::any();let d0:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();let prior:usize=kani::any();let kp0:usize=kani::any();let n:usize=kani::any();kani::assume((n==10||n==12)&&d0<=kp0&&kp0<n&&k<16&&c<32&&prior<1000&&index<262144);kani::assume(d0==0||idx[d0-1]!=index);kani::assume(k{'==' if effect=='inside' else '!='}d0);let old_i=idx[k];let old_v=val[k][c];let calls=Cell::new(prior);let mut d=d0;let mut key_position=kp0;key_position+=1;let leaf=batch_leaf(Port{{q:&q,tree:{tree},c,reply:&reply,calls:&calls}},{tree},&q);let outcome=if d>0&&same_batch_index(&idx,d-1,index){{if !same_batch_leaf(&val,d-1,leaf){{1u8}}else{{2u8}}}}else{{idx[d]=index;val[d]=leaf;d+=1;0u8}};'''
  expr='outcome==0&&key_position==kp0+1&&d==d0+1&&d<=key_position&&calls.get()==prior+1&&idx[k]=='+('index&&val[k][c]==reply[c]' if effect=='inside' else 'old_i&&val[k][c]==old_v')
  g.pair(f'leaf_{tree}_{effect}',body,expr)
if __name__=='__main__':g.publish('NBY_leaf','candidate.rs',41)
