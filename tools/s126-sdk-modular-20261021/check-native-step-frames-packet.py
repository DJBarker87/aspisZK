#!/usr/bin/env python3
"""Audit the concrete direct cleanup frame and SDK region binding; no solver replay."""
from pathlib import Path
import json,hashlib,subprocess,tempfile,re
R=Path(__file__).resolve().parents[2];T=R/'tools/s126-sdk-modular-20261021';E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-native-step-frames'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,d in load(E/'manifest.json')['files'].items():assert sha(E/rel)==d,rel
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc','.pyc'] for p in E.rglob('*'))
q=load(E/'qualification.json');assert sum(x['accepted'] for x in q['targets'].values())==2
for tag,x in q['targets'].items():
 P=E/'sources'/x['source'];i=load(E/(tag+'-input.json'));r=load(E/'receipts'/tag/'receipt.json');assert sha(P/'src/lib.rs')==i['source_sha256']==x['source_sha256']
 assert r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
 for package,pin in i.get('local_dependency_source_pins',{}).items():
  for rel,d in pin['files'].items():assert sha(E.parent/'sdk-release-allocator/dependencies'/package/rel)==d
 if not x['accepted']:continue
 assert r['exit_status']==0 and '-C opt-level=3' in i['env']['RUSTFLAGS'] and '--unwinding-assertions' in i['command']
 assert all(load(E/(tag+'-dependency-postcheck.json'))['unchanged'].values())
 checks=1865 if 'direct-frame' in tag else 1964;assert x['noncover_successes']==checks
 log=(E/'receipts'/tag/'stdout.log').read_text();assert f'0 of {checks} failed' in log and '2 of 2 cover properties satisfied' in log
 h=next(h for h in load(E/'metadata'/tag/'harness-metadata.json')['proof_harnesses'] if h['pretty_name']==x['harness'])
 assert h['attributes']['kind']==({'ProofForContract':{'target_fn':'ordered_cleanup'}} if 'direct-frame' in tag else 'Proof')
 assert not h['attributes']['verified_stubs'] and h['attributes']['stubs']==[{'original':'std :: alloc :: dealloc','replacement':'frozen_release_dealloc'}]
 producer='prepare-sdk-ordered-cleanup-direct-frame.py' if 'direct-frame' in tag else 'prepare-sdk-cleanup-region-bindings.py'
 with tempfile.TemporaryDirectory() as d:
  out=Path(d)/'source';subprocess.run(['python3',str(T/producer),str(out)],check=True,stdout=subprocess.DEVNULL)
  for rel in ['src/lib.rs','Cargo.toml']:assert (out/rel).read_bytes()==(P/rel).read_bytes(),(tag,rel)
# Binding probes alter only the harness; all actual cleanup operations remain exact.
def block(source,name):
 a=source.index('fn '+name+'(');b=source.index('{',a)+1;n=1
 while n:n+=(source[b]=='{')-(source[b]=='}');b+=1
 return source[a:b]
sources=[(E/'sources'/name/'src/lib.rs').read_text() for name in ['sdk-ordered-cleanup-direct-frame-v1','sdk-cleanup-region-bindings-v2']]
for name in ['finish_guard_shared','finish_guard_exclusive','destroy_owner','ordered_cleanup','frozen_release_dealloc']:assert block(sources[0],name)==block(sources[1],name),name
c=load(E/'cleanup-order/certificate.json');native=(E/'cleanup-order/native-stage1-goto.txt').read_text();fragment=(E/'cleanup-order/normal-copy-cleanup-goto.txt').read_text()
assert c['roles']==['checkpoint','proof_data','statement','public_data','checkpoint_data'] and c['unconditional_jumps']==[152,153,154,155,156,157,160]
assert sha(E/'cleanup-order/normal-copy-cleanup-goto.txt')==c['source_fragment_sha256'] and fragment in native
calls=[re.sub(r'^\s*(?:\d+:\s*)?','',s) for s in fragment.splitlines() if re.match(r'^\s*(?:\d+:\s*)?CALL ',s)];assert calls==c['normal_calls'] and len(calls)==6
inspection=load(E/'sdk-native-cleanup-goto-inventory-v1-input.json')
pair=load(E.parent/'sdk-native-success-bytes-pair/sdk-native-success-bytes-pair-v1-input.json')
assert c['program_sha256']==inspection['program_sha256']
assert c['source_sha256']==inspection['source_sha256']==pair['source_sha256']
assert inspection['command'][-1].endswith('/sdk-native-success-bytes-pair-v1/ready.out')
# The saved inspection pins its prepared program. The earlier pair packet pins
# raw GOTO and commands, not ready.out; do not invent an independent hash join.

print(json.dumps(dict(accepted=2,excluded=5,cleanup_checks=1865,binding_checks=1964,scope=q['scope'],remaining=q['remaining']),indent=2))
