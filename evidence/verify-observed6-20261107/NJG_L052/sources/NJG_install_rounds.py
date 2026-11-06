from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NJG_src';assert json.loads((B/'NJG_EXTRACTION_RESTORED.json').read_text())['restored'];pins=json.loads((B/'NJG_SOURCE_PINS.json').read_text());patch=[]
additions={
'crates/aspis-r1-cost-probe/src/r1_semantic.rs':(B/'NJG_rounds_driver.rs.txt').read_text(),
'crates/aspis-r1-cost-probe/src/r1_wire.rs':"#[cfg(kani)] pub fn NJG_round_transcript<H:Digest32>(hash:H,state:[u8;32],next_row:u8)->SemanticTranscript<H>{SemanticTranscript{hash,state,next_row}}\n",
'programs/r1-cost-probe/src/lib.rs':'''#[cfg(kani)] mod NJG_rounds_program {
 #[kani::proof] #[kani::unwind(200)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NJG_kmx::KMX_copy_nonoverlapping)] fn window(){aspis_r1_cost_probe::r1_semantic::NJG_rounds_driver::check(super::SolanaDigest,false);}
 #[kani::proof] #[kani::unwind(200)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NJG_kmx::KMX_copy_nonoverlapping)] fn control(){aspis_r1_cost_probe::r1_semantic::NJG_rounds_driver::check(super::SolanaDigest,true);}
}
'''}
for n,addition in additions.items():
 p=S/n;old=p.read_text();assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n];new=old+'\n'+addition;p.write_text(new);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJG_ROUNDS_INSTALL.patch').write_text(''.join(patch));(B/'NJG_SOURCE_PINS.json').write_text(json.dumps(pins));print('NJG one unrolled-round call-site cut installed')
