#!/usr/bin/env python3
"""Assess the already-merged H5 delta without relabelling historical pins."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/s2w-20261023';P=R/'docs/research/100bit-spend-path-20261013'
sha=lambda b:hashlib.sha256(b).hexdigest()
inv=json.loads((E/'source-inventory.json').read_text());path='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
old=subprocess.check_output(['git','show',inv['revision']+':'+path],cwd=R).decode();new=(R/path).read_text()
assert sha(old.encode())==inv['sources'][path]['sha256']
def fragment(s):
 a=s.index('fn require_zero(');i=s.index('{',a)+1;depth=1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
indexed=fragment(old);tail=fragment(new)
assert indexed!=tail and old.replace(indexed,tail)==new
kit=P/'lean-candidates/s4-zero-scanner-all-input-v1-20261023'
assert fragment((kit/'rust-source/indexed-r1_pool_adapter_owned.rs').read_text())==indexed
assert fragment((kit/'rust-source/tail-r1_pool_adapter_owned.rs').read_text())==tail
proof=kit/'sources/ZeroScannerAllInputEquivalenceV1.lean'
assert 'theorem all_input_source_equivalence' in proof.read_text()
record={'status':'pass','scope':'Historical requested D182/S10-repin2 ELF target is retained; do NOT reassign its pins to the later H5 source/artifact.',
 'historical_revision':inv['revision'],'source':path,'historical_sha256':sha(old.encode()),'current_sha256':sha(new.encode()),
 'inherited_change_commit':'60cb14bde27c219709a90beff94f21c1310e2d15',
 'only_adapter_file_delta':'require_zero indexed loop -> tail loop; EVERY other byte, including snapshot, native wrappers and extracted owned caller bodies, unchanged',
 'unchanged_wrappers_and_owned_callers':True,
 'helper_transport':{'source':str(proof.relative_to(R)),'sha256':sha(proof.read_bytes()),'theorem':'AspisR1ZeroScannerAllInputEquivalenceV1.all_input_source_equivalence','qualification':'Existing S4 all-input SDK-result equality for these exact two bodies; no replay, no candidate edit, not a whole-caller or adaptive-oracle transport proof'},
 'historical_release_pins':inv['release_pins'],
 'later_H5_application_receipt':'docs/research/100bit-spend-path-20261013/evidence/s9-h5-source-application-v1-20261023/application.json',
 'later_H5_candidate_elf':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',
 'later_H5_coherent_release_repin':'Separate owner obligation; historical S10 inventory is NOT asserted complete for H5',
 'our_shipped_file_edits':False,'our_elf_rebuilds':0}
out=E/'d189-inherited-source-delta.json'
if '--check' in sys.argv:assert json.loads(out.read_text())==record
else:out.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'pass','changed_helper':'require_zero','wrappers_unchanged':True,'old_ELFs_not_relabelled':True}))
