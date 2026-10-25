#!/usr/bin/env python3
"""Read-only native constructor/claim partition packet check; no compiler."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';T=Path(__file__).resolve().parent;P=E/'s1-native-prepared-claim-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():
 p=R/rel;assert sha(p)==h,rel
 assert p.suffix not in ['.olean','.ilean','.llbc','.goto','.out','.o','.a','.rlib','.rmeta','.so','.pyc']
b=json.loads((T/'source-binding.json').read_text());old=json.loads((E/'s1-native-prepared-20261025/source-kit-binding.json').read_text())
base=subprocess.check_output(['git','show',b['freeze']+':crates/aspis-r1-cost-probe/src/fast_pairing.rs'],cwd=R).decode()
j=b['dot_helpers'];assert hashlib.sha256(base.encode()).hexdigest()==j['original_sha256']
expected=base.replace(j['insertion_after'],j['insertion_after']+j['insertion'],1)+j['append']
assert hashlib.sha256(expected.encode()).hexdigest()==j['instrumented_sha256']
accepted=json.loads((P/'metrics.json').read_text())['accepted'];points=[]
for row in accepted:
 A=E/row['attempt'];i=json.loads((A/'input.json').read_text());r=json.loads((A/'receipt.json').read_text());point=row['point'];points.append(point)
 assert r['exit_status']==0 and r['swaps']==0 and r['watchdog_stop'] is None and r['verification_launched']
 assert all(r['source_unchanged'].values()) and all(r['tools_unchanged'].values())
 assert i['guard']['aggregate_rss_limit_bytes']==6*2**30
 assert '--unwinding-assertions' in r['command'] and '--unwindset' in r['command'] and 'uninit-checks' not in r['command']
 assert r['command'][r['command'].index('--harness')+1]==f'verifier::proofs::prepared_new_claim_point_{point}'
 for file,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(A/file)==r[key]
 for p in (A/'source').rglob('*'):
  if p.is_file() and p.name!='run.py':assert sha(p)==i['source_files'][str(p.relative_to(A/'source'))]
 S=A/'source/min/src/prepared_claim_native'
 for rel,h in b['unchanged_native_modules'].items():assert sha(S/rel)==h
 assert (S/'fast_pairing.rs').read_text()==expected
 for key in ['Error','View','Prepared','prepared_claim','Prepared_impl']:assert old['selected'][key] in (S/'verifier.rs').read_text()
 proof=(S/'proofs.rs').read_text();assert proof==(T/'proofs.rs').read_text()
 assert 'transmute' not in proof and 'kani::assume' not in proof and 'kani::stub(crate::verifier::prepared_claim' not in proof
 assert 'kani::stub(crate::weights::powers' not in proof and 'kani::stub(crate::transcript::' not in proof
 assert proof.count('#[kani::stub(')==63
 for value in ['same_e(value,POWERS[l])','sem.claims[p][l]','sem.extra[l]','sem.before_z1[l]','FIELDS[l].c0()','same_e(left,KG[k])','assert!(bytes.as_ptr()==Y1_PTR)','assert!(unsafe{CADD}==7)']:assert value in proof
 out=(A/'stdout.log').read_text();assert 'VERIFICATION:- SUCCESSFUL' in out
 assert re.search(r'0 of \d+ failed',out)
assert len(points)==len(set(points)) and set(points)<={0,1,2,3,4,5,6}
f=json.loads((E/'s1-native-prepared-claim-v2/receipt.json').read_text());assert f['exit_status']==-15 and f['watchdog_stop']=='wall watchdog'
assert f['peak_rss_bytes'] is None and f['swaps'] is None
assert all(json.loads((T/'reconstruction.json').read_text())['checks'].values())
print(json.dumps(dict(status='PASS',pins=len(m['files']),accepted_claim_partitions=points,remaining_claim_partitions=sorted(set(range(7))-set(points)),native_arithmetic_or_sdk_closed=False)))
