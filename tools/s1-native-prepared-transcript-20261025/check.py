#!/usr/bin/env python3
"""Read-only source/receipt audit; never launches a compiler or solver."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
P=E/'s1-native-prepared-transcript-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():assert sha(R/rel)==h,rel
b=json.loads((R/'tools/s1-native-prepared-transcript-20261025/source-binding.json').read_text())
frozen=subprocess.check_output(['git','show',b['freeze']+':crates/aspis-r1-cost-probe/src/weights.rs'],cwd=R).decode()
assert hashlib.sha256(frozen.encode()).hexdigest()==b['frozen_weights_whole_sha256']
assert b['exact_frozen_powers_body'] in frozen
transcript=subprocess.check_output(['git','show',b['freeze']+':crates/aspis-r1-cost-probe/src/transcript.rs'],cwd=R).decode()
assert hashlib.sha256(transcript.encode()).hexdigest()==b['whole_transcript_frozen_sha256']
old=json.loads((E/'s1-native-prepared-20261025/source-kit-binding.json').read_text())
for n in [1,2]:
 A=E/f's1-native-prepared-transcript-v{n}'
 i=json.loads((A/'input.json').read_text());r=json.loads((A/'receipt.json').read_text())
 assert r['exit_status']==0 and r['swaps']==0 and r['watchdog_stop'] is None
 assert all(r['source_unchanged'].values()) and all(r['tools_unchanged'].values())
 assert r['verification_launched']==(n==2)
 assert i['guard']['aggregate_rss_limit_bytes']==4*2**30
 assert '--unwinding-assertions' in r['command'] and 'uninit-checks' not in r['command']
 for file,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(A/file)==r[key]
 for p in (A/'source').rglob('*'):
  if p.is_file() and p.name!='run.py':assert sha(p)==i['source_files'][str(p.relative_to(A/'source'))]
 S=A/'source/min/src/prepared_transcript_native'
 assert (S/'transcript.rs').read_text()==transcript+'\n#[cfg(kani)]\npub(crate) fn proof_input<H:Digest32>(hash:H,state:[u8;32])->Transcript<H>{Transcript{state,hash}}\n'
 for rel,h in b['unchanged_native_modules'].items():assert sha(S/rel)==h
 for k in ['Error','View','Prepared','prepared_claim','Prepared_impl']:assert old['selected'][k] in (S/'verifier.rs').read_text()
 assert b['exact_frozen_powers_body'] in (S/'weights.rs').read_text()
 proof=(S/'proofs.rs').read_text();assert proof==(R/'tools/s1-native-prepared-transcript-20261025/proofs.rs').read_text()
 assert proof.count('#[kani::stub(')==6
 assert 'kani::stub(crate::transcript::' not in proof
 for k in ['fn digest_step','same_bytes(parts[0],&HASHES[13+2*k])','assert!(DIGEST_CALLS==30)','same_bytes(parts[0],&STATES[5])','same_bytes(block,&HASHES[31])']:assert k in proof,k
 assert 'kani::stub(crate::weights::powers' not in proof
 assert 'kani::assume' not in proof and 'transmute' not in proof
 for s in ['same_e(left,POWERS[n])','same_e(right,SCALARS[0])','assert!(MUL_CALLS==28)','powers[0]=E::ONE','same_powers(g,&POWERS)','assert!(g as *const [E;29]==G_PTR)']:assert s in proof,s
out=(E/'s1-native-prepared-transcript-v2/stdout.log').read_text()
assert 'VERIFICATION:- SUCCESSFUL' in out and '3 of 3 cover properties satisfied' in out
print(json.dumps(dict(status='PASS',pins=len(m['files']),covers=3,scope='native constructor, powers and complete transcript framing under sampler/query/claim/multiplication cuts and scripted digest; no SDK/source closure')))
