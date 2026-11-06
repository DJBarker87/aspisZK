"""Retain safe reference bodies and exact frozen provenance; no compiler or extraction."""
from pathlib import Path
import subprocess,hashlib,json
from NJQ_patch import write_patch
E=Path(__file__).resolve().parent
paths={'identity':('format.rs','decode_pool_identity_v1'),'checkpoint':('pair_forest_accounts.rs','decode_pool_v1_pair_forest_checkpoint_v1'),'master':('pair_forest_accounts.rs','decode_pool_v1_pair_forest_master_v1'),'entry':('verifier_registry.rs','decode_verifier_registry_entry_v1'),'registry':('verifier_registry.rs','decode_verifier_registry_v1')}
text='''use super::*;
use aspis_core::field::{M31,P};
use crate::pool_v1::format::*;
use crate::pool_v1::verifier_registry::*;
// Hand reference input for (ah) review. Native loop bodies are checked ONE
// iteration only; these full Rust functions are not run as whole-buffer Kani jobs.
'''
rows=[]
for row,(file,fn) in paths.items():
 path='crates/aspis-statement/src/pool_v1/'+file
 raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path]);src=raw.decode();start=src.index('pub fn '+fn+'(');i=src.index('{',start)+1;level=1
 while level:
  if src[i]=='{':level+=1
  elif src[i]=='}':level-=1
  i+=1
 body=src[start:i];reference=body.replace('pub fn '+fn+'(','pub fn '+fn+'_ref(',1)
 text+='\n'+reference+'\n'
 rows.append(dict(member=row,path=path,function=fn,reference=fn+'_ref',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',file_sha256=hashlib.sha256(raw).hexdigest(),source_function_sha256=hashlib.sha256(body.encode()).hexdigest(),reference_sha256=hashlib.sha256(reference.encode()).hexdigest(),lines=[src[:start].count('\n')+1,src[:i].count('\n')+1],change='function name only; child calls remain the frozen CLOSED/candidate child boundaries',credit='NONE: provenance/hand-transcription input, never standalone native or emitted-body credit'))
write_patch('NJQ_reference',text)
(E/'NJQ_REFERENCES.json').write_text(json.dumps(rows,indent=1)+'\n')
print('Five exact safe Rust reference bodies retained; no extraction or whole-loop verification.')
