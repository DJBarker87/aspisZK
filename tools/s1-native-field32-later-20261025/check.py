#!/usr/bin/env python3
"""Read-only audit of exact native32-byte selected-record decoder evidence."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';P=E/'s1-native-field32-later-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():
 p=R/rel;assert sha(p)==h,rel
 assert p.suffix not in ['.olean','.ilean','.llbc','.goto','.out','.o','.a','.rlib','.rmeta','.so','.pyc']
b=json.loads((T/'source-binding.json').read_text());original=subprocess.check_output(['git','show',b['source']+':crates/aspis-r1-cost-probe/src/weights.rs'],cwd=R).decode();assert hashlib.sha256(original.encode()).hexdigest()==b['whole_weights_sha256'];assert b['selected_field']in original
for n in [3,4]:
 A=E/f's1-native-field32-later-v{n}';r=json.loads((A/'receipt.json').read_text());i=json.loads((A/'input.json').read_text());assert r['exit_status']==0 and r['swaps']==0 and r['watchdog_stop']is None
 assert all(r['source_unchanged'].values())and all(r['tools_unchanged'].values());assert r['verification_launched']==(n==4)
 assert '--unwinding-assertions'in r['command']and 'uninit-checks'not in r['command']
 for file,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(A/file)==r[key]
 for p in(A/'source').rglob('*'):
  if p.is_file()and p.name!='run.py':assert sha(p)==i['source_files'][str(p.relative_to(A/'source'))]
 assert b['selected_field']in(A/'source/field32_later/src/weights.rs').read_text()
 proof=(A/'source/field32_later/src/proofs.rs').read_text();assert proof==(T/'proofs.rs').read_text()
 assert all(s not in proof for s in ['kani::stub','kani::assume','transmute'])
 assert '[u8;928]'in proof and '%29'in proof and '32*index+4*j+b'in proof
 for s in ['actual.to_limbs()','actual.c0()','actual.c1()','words[7]','index==0','index==28']:assert s in proof
for source,h in b['active_core'].items():
 assert hashlib.sha256(subprocess.check_output(['git','show',b['source']+':'+source],cwd=R)).hexdigest()==h
# Cargo metadata, not inherited inactive cache inventory, identifies actual core.
for n in [3,4]:
 A=E/f's1-native-field32-later-v{n}';md=json.loads((A/'metadata.stdout.json').read_text());core=[p for p in md['packages']if p['name']=='aspis-core'];assert len(core)==1 and '/later-core-workspace/'in core[0]['manifest_path']
 i=json.loads((A/'input.json').read_text())
 for source,h in b['active_core'].items():assert i['source_files']['later-core-workspace/'+source]==h
out=(E/'s1-native-field32-later-v4/stdout.log').read_text();assert '0 of 306 failed'in out and '2 of 2 cover properties satisfied'in out
print(json.dumps(dict(status='PASS',pins=len(m['files']),checks=306,covers=2,scope='Later4bb3 full-core native field TOTAL on selected canonical32-byte frame at any of29 indices in928-byte input; remaining896 bytes arbitrary. No stub, no SDK/native broad totality claim.')))
