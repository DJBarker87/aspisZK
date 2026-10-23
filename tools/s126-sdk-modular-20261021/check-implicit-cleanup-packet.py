#!/usr/bin/env python3
"""Audit source-only actual implicit cleanup/copy certificates, no solver replay."""
from pathlib import Path
import json,hashlib,subprocess,tempfile,re
R=Path(__file__).resolve().parents[2];T=R/'tools/s126-sdk-modular-20261021';E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-implicit-cleanup'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,d in load(E/'manifest.json')['files'].items():assert sha(E/rel)==d,rel
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc','.pyc'] for p in E.rglob('*'))
q=load(E/'qualification.json');accepted=[]
for tag,row in q['targets'].items():
 P=E/'sources'/row['source'];i=load(E/(tag+'-input.json'));r=load(E/'receipts'/tag/'receipt.json');assert sha(P/'src/lib.rs')==i['source_sha256']==row['source_sha256']
 assert r==row['receipt'] and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
 for package,pin in i['local_dependency_source_pins'].items():
  for rel,d in pin['files'].items():assert sha(E.parent/'sdk-release-allocator/dependencies'/package/rel)==d
 assert all(load(E/(tag+'-dependency-postcheck.json'))['unchanged'].values())
 if not row['accepted']:
  assert r['exit_status']!=0;continue
 accepted.append(tag);assert r['exit_status']==0 and '-C opt-level=3' in i['env']['RUSTFLAGS'] and '--unwinding-assertions' in i['command']
 log=(E/'receipts'/tag/'stdout.log').read_text();assert f"0 of {row['checks']} failed" in log and '2 of 2 cover properties satisfied' in log
 h=next(h for h in load(E/'metadata'/tag/'harness-metadata.json')['proof_harnesses'] if h['pretty_name']=='proofs::actual_sdk_ordered_cleanup')
 assert h['attributes']['kind']=={'ProofForContract':{'target_fn':'ordered_cleanup'}} and not h['attributes']['verified_stubs']
 assert h['attributes']['stubs']==[{'original':'std :: alloc :: dealloc','replacement':'frozen_release_dealloc'}]
 producer='prepare-sdk-implicit-copy-cleanup-frame.py' if 'copy-cleanup' in tag else 'prepare-sdk-implicit-cleanup-frame.py'
 with tempfile.TemporaryDirectory() as d:
  out=Path(d)/'source';subprocess.run(['python3',str(T/producer),str(out)],check=True,stdout=subprocess.DEVNULL)
  for rel in ['src/lib.rs','Cargo.toml']:assert (out/rel).read_bytes()==(P/rel).read_bytes(),(tag,rel)
 c=load(E/'order'/tag/'certificate.json');fragment=E/'order'/tag/'implicit-cleanup-goto.txt'
 assert c['source_sha256']==i['source_sha256'] and c['program_sha256']==row['prepared_goto_sha256'] and c['raw_goto_sha256']==row['raw_goto_sha256']
 assert c['fragment_sha256']==sha(fragment) and c['roles']==['reply','proof','statement','public','checkpoint']
 source=(P/'src/lib.rs').read_text();a=source.index('fn ordered_cleanup(');b=source.index('#[kani::proof_for_contract(ordered_cleanup)]',a);body=source[a:b]
 assert 'implicit_cleanup(counters,checkpoint,public,statement,candidate,proof,reply' in body
 assert not any(x in body for x in ['ManuallyDrop','drop_in_place','finish_guard','destroy_owner'])
 if 'copy-cleanup' in tag:assert 'checkpoint.copy_from_slice(&reply);' in body
assert len(accepted)==1
print(json.dumps(dict(accepted=accepted,excluded=2,remaining=q['remaining']),indent=2))
