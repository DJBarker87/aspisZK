from pathlib import Path
import hashlib,json,re
w=Path('/home/dombarker/project-offloads/aspis-r1-public-preparation-step-20261016');old=w.parent/'aspis-r1-public-preparation-20261016'
sha=lambda b:hashlib.sha256(b).hexdigest()
def strip(s):return re.sub(r"Source: 'lib.rs', lines [0-9:]+-[0-9:]+", "Source: 'lib.rs', lines PINNED_SEPARATELY",s)
out={}
for name in ['Types.lean','Funs.lean']:
 before=(old/'generated/AspisR1PublicPreparation'/name).read_bytes();raw=(w/'generated/AspisR1PublicPreparation'/name).read_bytes();reduced=raw.decode();added=''
 if name=='Funs.lean':
  start=reduced.index('/-- [aspis_r1_public_preparation::r1_wire::{aspis_r1_public_preparation::r1_wire::SemanticTranscript<H>}::sample_block_validated]')
  end=reduced.index('/-- [aspis_r1_public_preparation::r1_semantic::public_transcript::',start)
  added=reduced[start:end];reduced=reduced[:start]+reduced[end:];assert added.count('\ndef ')==2
 assert strip(before.decode())==strip(reduced)
 out[name]={'old_producing_commit':'f6521c1249cef35b01b2e343445ec795d9ec82eb','old_sha256':sha(before),'new_sha256':sha(raw),'same_after_removing_only_added_declarations_and_source_location_comments':True,'common_normalized_sha256':sha(strip(reduced).encode()),'added_declarations_sha256':sha(added.encode()) if added else None}
(w/'original-definition-comparison.json').write_text(json.dumps(out,indent=2)+'\n')
llbc=json.loads((w/'PublicPreparation.llbc').read_text());t=llbc['translated'];ids=[f['def_id'] for f in t['fun_decls'] if f and f['item_meta']['name'][-1].get('Ident',[''])[0] in ['sample_block_validated','sample_validated_entry']]
ordered=t['ordered_decls'];assert len(ids)==2
for i in ids:assert {'Fun':{'NonRec':i}} in ordered
(w/'root-selection-audit.json').write_text(json.dumps({'actual_step_and_wrapper_ids':ids,'ordered_decls':ordered,'llbc_sha256':sha((w/'PublicPreparation.llbc').read_bytes())},indent=2)+'\n')
print('PASS original34 definitions unchanged; new method+wrapper present in ordered_decls')
