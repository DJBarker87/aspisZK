"""Source-pinned digest cuts. Cuts preserve each frozen statement verbatim."""
from pathlib import Path
import re,json,hashlib,lzma
E=Path(__file__).resolve().parent;fs=json.loads(lzma.decompress((E/'NGQ_FROZEN_INPUTS.json.xz').read_bytes()));src=fs['crates/aspis-r1-cost-probe/src/transcript.rs']
s='''use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]
struct NGQ_Oracle<'a> { log: &'a Cell<(usize,u8,u8,u8,u8)>, replies: &'a [[u8;32];2], window: usize }
impl aspis_core::Digest32 for NGQ_Oracle<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(parts.len(),2);assert_eq!(parts[0].len(),32);assert_eq!(parts[1].len(),1);
  let (n,s0,t0,s1,t1)=self.log.get(); assert!(n<2);
  if n==0 {self.log.set((1,parts[0][self.window],parts[1][0],s1,t1));}
  else {self.log.set((2,s0,t0,parts[0][self.window],parts[1][0]));}
  self.replies[n]
 }
}
impl<H:aspis_core::Digest32> Transcript<H> {
''';pins=[]
for k in range(8):
 pattern=rf'blocks\[{k}\]=self.hash.digest\(&\[&state,&\[1\]\]\);\s*advances\[{k}\]=self.hash.digest\(&\[&state,&\[2\]\]\);state=advances\[{k}\];'
 m=re.search(pattern,src);assert m;body=m[0]
 pins.append(dict(stage=k,source_start=m.start(),source_end=m.end(),sha256=hashlib.sha256(body.encode()).hexdigest()))
 s+=f'fn NGQ_pair{k}(&self,mut blocks:[[u8;32];8],mut advances:[[u8;32];8],mut state:[u8;32])->([[u8;32];8],[[u8;32];8],[u8;32]) {{\n{body}\n(blocks,advances,state)\n}}\n'
s+='}\n'
for k in range(8):
 s+=f'''#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_pair{k}() {{
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let state:[u8;32]=kani::any();let replies:[[u8;32];2]=kani::any();
 let j:usize=kani::any();let p:usize=kani::any();kani::assume(j<32 && p<8);
 let log=Cell::new((0usize,0u8,0u8,0u8,0u8));
 let hash=NGQ_Oracle{{log:&log,replies:&replies,window:j}};
 let t=Transcript{{state,hash}};
 let (b,a,final_state)=t.NGQ_pair{k}(blocks,advances,state);
 let correct=log.get()==(2,state[j],1,state[j],2)
  && b[p][j]==(if p=={k} {{replies[0][j]}} else {{blocks[p][j]}})
  && a[p][j]==(if p=={k} {{replies[1][j]}} else {{advances[p][j]}})
  && final_state[j]==replies[1][j] && t.state[j]==state[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(b[{k}][0]==(replies[0][0]^1));
}}
'''
(E/'NGQ_pairs_harness.rs.txt').write_text(s);(E/'NGQ_PAIR_CUTS.json').write_text(json.dumps(pins,indent=1)+'\n')
