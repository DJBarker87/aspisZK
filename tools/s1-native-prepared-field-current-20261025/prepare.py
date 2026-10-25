#!/usr/bin/env python3
"""Re-pin the field-integrated native caller to ledger compiler source4bb3; source only."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1]);F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-field-20261025/prepare.py'),str(O)],check=True)
def git(p):return subprocess.check_output(['git','show',F+':'+p],cwd=R)
old=json.loads((O/'predecessor-binding.json').read_text());base=O/'min/src/prepared_claim_native'
# Pin exact complete selected native definitions; do not infer whole-file equality.
for key,row in old['selected_spans'].items():
 s=git('crates/aspis-r1-cost-probe/src/'+row['file']).decode()
 assert old['selected'][key]in s,key
for p in (O/'core-workspace/crates/aspis-core').rglob('*'):
 if p.is_file():p.write_bytes(git(str(p.relative_to(O/'core-workspace'))))
helpers=json.loads((R/'tools/s1-native-prepared-claim-20261025/source-binding.json').read_text())['dot_helpers']
s=git('crates/aspis-r1-cost-probe/src/fast_pairing.rs').decode()
assert s.count(helpers['insertion_after'])==1
(base/'fast_pairing.rs').write_text(s.replace(helpers['insertion_after'],helpers['insertion_after']+helpers['insertion'],1)+helpers['append'])
for name in ['transport.rs','trace.rs','sampler.rs']:
 p=O/'min/src/sampler.rs'if name=='sampler.rs'else base/name
 assert p.read_bytes()==git('crates/aspis-r1-cost-probe/src/'+name),name
for name,tail in [('transcript.rs','\n#[cfg(kani)]\npub(crate) fn proof_input<H:Digest32>(hash:H,state:[u8;32])->Transcript<H>{Transcript{state,hash}}\n'),('r1_wire.rs','\n#[cfg(kani)]\nimpl<H:Digest32> SemanticTranscript<H>{pub(crate) fn proof_input(hash:H,state:[u8;32],next_row:u8)->Self{Self{state,hash,next_row}}}\n')]:
 assert (base/name).read_text()==git('crates/aspis-r1-cost-probe/src/'+name).decode()+tail
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'current-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=F,files=files,selected_complete_definitions_checked=list(old['selected_spans']),current_core_source_count=len(list((O/'core-workspace/crates/aspis-core/src').rglob('*.rs'))),remaining='Native focused checks still required.8 normal primitive cuts and canonical928-byte payload; actual SDK/init/extraction/runtime/oracle/release remain open. No whole compiled release identity inferred.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',freeze=F,files=len(files),compiler_launched=False)))
