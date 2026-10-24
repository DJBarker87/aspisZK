#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
legacy=E/'modular-host/sources/powers-control-v1';cut=json.loads((legacy/'source-cut.json').read_text())
assert sha(legacy/'src/lib.rs')==cut['code_sha256']
refs=['b2727acd3abf79315d18b754a260f58f4b1c6326','29cbab431742f7e899870595167efa193a379f0a','25866ec331cc7ce27dd9956609c11d32fa8fa58a']
def powers(text):
 a=text.index('pub fn powers<');start=text.index('{',a);depth=1;end=start+1
 while depth:
  depth+=(text[end]=='{')-(text[end]=='}');end+=1
 return text[a:end]
rows={};native={}
for ref in refs:
 data=subprocess.check_output(['git','-C',str(R),'show',ref+':'+cut['path']]);body=powers(data.decode())
 expected=cut['original'] if ref==refs[0] else cut['candidate'].replace('candidate_powers','powers',1)
 assert body==expected,(ref,'powers body differs')
 rows[ref]={'whole_weights_sha256':hashlib.sha256(data).hexdigest(),'powers_sha256':hashlib.sha256(body.encode()).hexdigest(),'kind':'historical_from_fn' if ref==refs[0] else 'adopted_early_return','body':body}
for path in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs']:
 hashes={ref:hashlib.sha256(subprocess.check_output(['git','-C',str(R),'show',ref+':'+path])).hexdigest() for ref in refs}
 assert len(set(hashes.values()))==1,path
 native[path]=hashes
reused=[legacy/'src/lib.rs',legacy/'source-cut.json',legacy/'Cargo.toml',legacy/'Cargo.lock',E/'modular-host/std/kani-library-pins.json',E/'modular-host/std/kani-contract-source-pins.json',E/'s1-native-word-control-source-pins.json',B/'lean-candidates/s1-early-return-powers-proved-candidate-20261020/manifest.json',B/'lean-candidates/s1-early-return-powers-proved-candidate-20261020/extraction-input/source-pins.json',B/'evidence/s1-current-wide-exact-field-20261020/manifest.json']
reused += [B/'lean-candidates/s1-claim-parser-and-inner-trace-20261020/sources/CurrentClaimPowersInstance.lean',B/'lean-candidates/s1-early-return-powers-proved-candidate-20261020/check-source-model.py']
for name in ['powers7-control-v1','powers29-control-v1']:

 d=E/'modular-host/receipts'/name;r=json.loads((d/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 log=(d/'stdout.log').read_text();assert '0 of 369 failed' in log and 'VERIFICATION:- SUCCESSFUL' in log
 reused += [d/n for n in ['receipt.json','stdout.log','stderr.log','time.log']]
out={'schema':'focused-extractor-proof-packet-v1','native_source_pin_reuse':{'path':cut['path'],'selected_original_powers_body':cut['original'],'separate_source_pins':rows,'arithmetic_files_byte_identical':native,'current_adopted_overlay':refs[2],'adoption_revision':refs[1],'new_source_adoption':False},'reused_source_evidence':{str(p.relative_to(R)):sha(p) for p in reused},'qualification':'Current adopted powers body is byte-identical to the checked early-return reference, and complete field files are unchanged. Historical fixed N7/N29 from_fn/candidate normal-return comparison is REUSED ONLY as historical evidence. No new adoption or ELF rebuild; source helper re-pin does not close native Std/SDK/artifact or unconditional R22. Historical host-wide aggregate accounting remains unverified as corrected separately.'}
p=E/'s1-powers-callback-source-pins.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'selected_historical_source_pins':len(rows),'reused_evidence_files':len(reused),'new_native_job':False}))
