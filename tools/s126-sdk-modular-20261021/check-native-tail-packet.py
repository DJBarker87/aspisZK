#!/usr/bin/env python3
"""Check source-only post-first/leaf-links receipts without solver replay."""
from pathlib import Path
import json,hashlib,re,tempfile,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-native-tail'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,d in load(E/'manifest.json')['files'].items():assert sha(E/rel)==d,rel
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc'] for p in E.rglob('*'))
q=load(E/'qualification.json');assert len(q['accepted'])==4
checks={'sdk-native-post-first-tail-root1-check-v5':2083,'sdk-native-post-first-tail-root2-check-v5':2085,'sdk-native-post-first-tail-root0-window0-check-v6':2084,'sdk-native-tail-leaf-links-check-v1':2187}
for tag,row in q['accepted'].items():
 P=E/'sources'/row['source'];r=load(E/'receipts'/tag/'receipt.json');i=load(E/(tag+'-input.json'));log=(E/'receipts'/tag/'stdout.log').read_text()
 assert sha(P/'src/lib.rs')==row['source_sha256']==i['source_sha256'];assert sha(E/'receipts'/tag/'receipt.json')==row['receipt_sha256']
 assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
 assert f'0 of {checks[tag]} failed' in log and '3 of 5 cover properties satisfied' in log
 assert row['assertions']==checks[tag] and '-C opt-level=3' in i['env']['RUSTFLAGS'] and '--unwinding-assertions' in i['command']
 assert all(load(E/(tag+'-dependency-postcheck.json'))['unchanged'].values())
 for package,pin in i['local_dependency_source_pins'].items():
  for rel,d in pin['files'].items():assert sha(E/'dependencies'/package/rel)==d
 h=[x for x in load(E/'metadata'/tag/'harness-metadata.json')['proof_harnesses'] if x['pretty_name']=='proofs::native_post_first_tail'];assert len(h)==1;h=h[0]
 assert h['attributes']['kind']=='Proof' and not h['attributes']['stubs'] and h['attributes']['verified_stubs']==['encoded_finish']
 with tempfile.TemporaryDirectory() as d:
  out=Path(d)/'source';args=['python3',str(R/'tools/s126-sdk-modular-20261021'/('prepare-sdk-native-tail-links.py' if 'leaf-links' in tag else 'prepare-sdk-native-tail.py')),str(out)]
  if 'leaf-links' not in tag:args += ['0','0'] if 'window0' in tag else ['1' if 'root1' in tag else '2']
  subprocess.run(args,check=True)
  for rel in ['src/lib.rs','Cargo.toml']:assert (out/rel).read_bytes()==(P/rel).read_bytes(),(tag,rel)
 # The exact native_finish/encoded_finish helper and copied leaf proof are unchanged.
 source=(P/'src/lib.rs').read_text();owner=(E.parent/'sdk-parent-cuts/sources/sdk-finish-fixed-frame-v5/src/lib.rs').read_text()
 a=owner.index('fn native_finish(');b=owner.index('#[cfg(kani)] mod proofs',a);assert owner[a:b] in source
for root in [1,2]:
 a=load(E/'cover-audits'/str(root)/'audit.json');tag=f'sdk-native-post-first-tail-root{root}-check-v5'
 assert a['source_sha256']==q['accepted'][tag]['source_sha256'] and a['program_sha256']==q['accepted'][tag]['prepared_goto_sha256']
 assert len(set(x['description'] for x in a['reached_source_covers']))==3
 r=load(E/'receipts'/(tag+'-covers-v2')/'receipt.json');assert r['exit_status']==10 and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
print(json.dumps(dict(accepted=q['accepted'],excluded=len(q['excluded']),scope=q['scope'],remaining=q['remaining']),indent=2))
