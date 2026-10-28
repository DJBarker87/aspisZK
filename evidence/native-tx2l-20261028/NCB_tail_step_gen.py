from NCB_generate import *
import json
p='crates/aspis-r1-cost-probe/src/fast_pairing.rs'
s=current(p)
extra='''\n#[cfg(kani)] pub(crate) fn NCB_invariant(s:&EbyKDot)->bool {
 let a=canonical::NBQ_sums(&s.c0);let b=canonical::NBQ_sums(&s.c1);
 let limit=(s.count as u64)*10737418238;
 s.count<=4096&&a[0]<=limit&&a[1]<=limit&&a[2]<=limit&&a[3]<=limit&&b[0]<=limit&&b[1]<=limit&&b[2]<=limit&&b[3]<=limit
}\n'''
out=''.join(difflib.unified_diff(s.splitlines(True),(s+extra).splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='crates/aspis-r1-cost-probe/src/fast_dots.rs';s=current(p)
frozen=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
lines=[l.strip() for l in frozen.splitlines() if 'tail.push(' in l]
assert len(lines)==3
text=r'''
#[cfg(kani)] mod NCB_tail_step {
 use super::*;
 static mut PTR:*mut EbyKDot=core::ptr::null_mut();static mut COUNT:usize=0;static mut CALLS:usize=0;
 static mut G:[u32;8]=[0;8];static mut Q:[u32;4]=[0;4];
 fn word(q:&[u8;608],at:usize)->u32{u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])}
 fn push(t:&mut EbyKDot,v:WideExact,k:QM31)->Result<(),()>{unsafe{
  assert!(core::ptr::eq(t,PTR));assert!(CALLS==0);CALLS=1;
  assert!(crate::fast_pairing::NBQ_count(t)==COUNT&&COUNT<3);assert!(crate::fast_pairing::NCB_invariant(t));
  let limbs=v.to_limbs();let j:usize=kani::any();kani::assume(j<8);assert!(limbs[j]==G[j]&&limbs[j]<2147483647);
  assert!(k.c0.a.0==Q[0]&&k.c0.b.0==Q[1]&&k.c1.a.0==Q[2]&&k.c1.b.0==Q[3]);
  assert!(k.c0.a.0<2147483647&&k.c0.b.0<2147483647&&k.c1.a.0<2147483647&&k.c1.b.0<2147483647);
  crate::fast_pairing::NBQ_advance(t);kani::assume(crate::fast_pairing::NCB_invariant(t));Ok(())
 }}
'''
for kind in range(3):
 cut=lines[kind]
 if kind==1:cut='let offset0=480+slot*32+0*16;'+cut
 if kind==2:cut='let offset1=480+slot*32+1*16;'+cut
 text+=f'fn cut{kind}(q:&[u8;608],g:&[WideExact;29],slot:usize,tail:&mut EbyKDot)'+'{'+cut+'}\n'
 text+='#[kani::proof] #[kani::unwind(512)]\n'+attrs+'#[kani::stub(EbyKDot::push,push)]\n'+f'fn push{kind}()'+'{\n'
 text+='''let q:[u8;608]=kani::any();let raw:[[u32;8];29]=kani::any();let mut g:[WideExact;29]=unsafe{core::mem::transmute(raw)};
 let slot:usize=kani::any();kani::assume(slot<4);let limbs:[u32;8]=kani::any();for j in 0..8{kani::assume(limbs[j]<2147483647);}
 '''+f'g[{[28,26,27][kind]}]=WideExact::from_limbs(limbs).unwrap();let at='+('slot*120+104;' if kind==0 else f'480+slot*32+{(kind-1)*16};')+'\n'
 text+='''let input=[word(&q,at),word(&q,at+4),word(&q,at+8),word(&q,at+12)];for j in 0..4{kani::assume(input[j]<2147483647);}
 '''+f'let mut tail=crate::fast_pairing::NBQ_state({kind});kani::assume(crate::fast_pairing::NCB_invariant(&tail));\n'
 text+=f'unsafe{{PTR=&mut tail;COUNT={kind};CALLS=0;G=limbs;Q=input;}}\ncut{kind}(&q,&g,slot,&mut tail);\n'
 text+=f'unsafe{{assert!(CALLS==1);}}assert!(crate::fast_pairing::NBQ_count(&tail)=={kind+1});assert!(crate::fast_pairing::NCB_invariant(&tail));\n'+'}\n'
text+='}\n'
out+=''.join(difflib.unified_diff(s.splitlines(True),(s+text).splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NCB_tail_step.patch').write_text(out)
(E/'NCB_TAIL_SOURCE.json').write_text(json.dumps({'source':p,'revision':'4bb3b3f5','exact_calls':lines,'sha256':[hashlib.sha256(l.encode()).hexdigest() for l in lines],'stub':'one EbyKDot::push overapproximation to invariant/count only','paired_theorem':'NBQ_PublicInvariant.step','domain':'canonical SAME g coefficient, canonical SAME q decoder, count0/1/2, NBQ_PublicInvariant.Inv; no numeric poststate equality is asserted'},indent=2)+'\n')
