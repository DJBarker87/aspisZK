from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent.parent
s=(E/'inactive-owner/lib.rs').read_text();table=re.search(r'MASKS:\[u16;64\]=(\[.*?\]);',s,re.S)[1]
p=E/'native/lib.rs';t=p.read_text()
if 'inactive-binding.rs' not in t:t+='\ninclude!("inactive-binding.rs");\n'
p.write_text(t)
(E/'native/inactive-binding.rs').write_text('''
const ACTIVE_MASKS:[u16;64]='''+table+''';
fn native_s2_row(j:usize)->usize {
 const TAU:[usize;5]=[3,4,2,0,1];let mut out=0;
 for d in 0..5 {out|=((j>>(2*d))&3) << (2*TAU[d]);}out
}
fn native_s2_inactive(r:usize)->Result<bool,u8> {
 if r>=1024 {return Err(1);}
 Ok((ACTIVE_MASKS[r/16]>>(r%16))&1==0)
}
fn owner_s2_row(j:usize)->usize {(j/64)%4+4*((j/256)%4)+16*((j/16)%4)+64*(j%4)+256*((j/4)%4)}
fn owner_s2_inactive(j:usize)->bool {let r=owner_s2_row(j);(ACTIVE_MASKS[r/16]>>((r%16) as u32))&1==0}
#[cfg(kani)] mod inactive_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(66)] fn complete_s2_inactive() {
  let j:usize=kani::any();kani::assume(j<1024);
  assert_eq!(native_s2_row(j),owner_s2_row(j));
  assert_eq!(native_s2_inactive(native_s2_row(j)),Ok(owner_s2_inactive(j)));
 }
}
''')
paths=['crates/aspis-core/src/r0/opening.rs','crates/aspis-r1-cost-probe/src/transport.rs','crates/aspis-r1-cost-probe/src/weights.rs']
(E/'pins/inactive-native-spans.json').write_text(json.dumps(dict(inputs={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths},binding='Complete S2 row permutation and inactive Result for every legal coefficient index, using the full literal 64-entry source table; no callee abstraction.'),indent=2)+'\n')
