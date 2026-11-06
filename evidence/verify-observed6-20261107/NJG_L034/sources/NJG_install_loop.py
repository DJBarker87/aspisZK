from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NJG_src';pins=json.loads((B/'NJG_SOURCE_PINS.json').read_text());frozen=json.loads((B/'NJG_FROZEN_FILE_PINS.json').read_text());patch=[]
additions={
'crates/aspis-r1-cost-probe/src/r1_semantic.rs':(B/'NJG_claims_loop.rs.txt').read_text(),
'crates/aspis-r1-cost-probe/src/r1_wire.rs':"#[cfg(kani)] pub fn NJG_claims_record(framed:&[u8])->ValidatedRecord<'_>{ValidatedRecord{row:25,framed}}\n",
'programs/r1-cost-probe/src/lib.rs':'''#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NJG_kmx;
#[cfg(kani)] mod NJG_claims_loop_program {
 #[kani::proof] #[kani::unwind(3720)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NJG_kmx::KMX_copy_nonoverlapping)] fn window(){aspis_r1_cost_probe::r1_semantic::NJG_claims_loop::check(false);}
 #[kani::proof] #[kani::unwind(3720)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NJG_kmx::KMX_copy_nonoverlapping)] fn control(){aspis_r1_cost_probe::r1_semantic::NJG_claims_loop::check(true);}
}
'''}
for n,addition in additions.items():
 p=S/n;old=p.read_text();new=old+'\n'+addition
 if n.startswith('programs/') :new='#![cfg_attr(kani,feature(allocator_api))]\n'+new
 p.write_text(new);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();frozen.pop(n,None);patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJG_LOOP_INSTALL.patch').write_text(''.join(patch));(B/'NJG_SOURCE_PINS.json').write_text(json.dumps(pins));(B/'NJG_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen));print('NJG one claims iteration stages installed')
