from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
raw=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/compact.rs'],text=True)
def function(name):
 a=raw.index('pub fn '+name+'(');b=raw.index('{',a);depth=1;i=b+1
 while depth:depth+=(raw[i]=='{')-(raw[i]=='}');i+=1
 return raw[a:i]
ref=(E/'NGD_references.rs.txt').read_text()
ref+='''
#[derive(Clone,Copy)]pub enum CodecError{Length,NonZeroHigh,NonCanonical}
pub const SEMANTIC_ROWS:u8=27;
pub const COMPACT_SEMANTIC:usize=7015;
pub const LOGICAL_SEMANTIC:usize=13831;
fn row_shape(row:u8)->Option<(u8,usize)>{shape(row)}
fn compact_row(row:u8)->bool{row>=14}
'''+function('expand_values')+'\n'+function('expand_semantic')+'\n'
(E/'NGD_references.rs.txt').write_text(ref)
p=E/'NGD_extract.py';s=p.read_text().replace("'NGD_SlotRef':'crate::slot_offset'", "'NGD_SlotRef':'crate::slot_offset','NGD_ExpandRef':'crate::expand_semantic'");p.write_text(s)
(E/'NGD_EXPAND_REFERENCE_PINS.json').write_text(json.dumps(dict(frozen_source_sha256=hashlib.sha256(raw.encode()).hexdigest(),expand_values_sha256=hashlib.sha256(function('expand_values').encode()).hexdigest(),expand_semantic_sha256=hashlib.sha256(function('expand_semantic').encode()).hexdigest(),method='Exact two function bodies, standalone full CodecError; constants fixed to proved release values; existing shape function returns complete row table',claim='REFERENCE EXTRACTION ONLY; never a native or composed certificate'),indent=2)+'\n')
