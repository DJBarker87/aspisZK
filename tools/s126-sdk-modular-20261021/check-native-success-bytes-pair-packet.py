#!/usr/bin/env python3
"""Check audited source-only native constructor evidence, without proof replay."""
from pathlib import Path
import json,hashlib,tempfile,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-native-success-bytes-pair'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,d in load(E/'manifest.json')['files'].items():assert sha(E/rel)==d,rel
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc'] for p in E.rglob('*'))
a=load(E/'case/success-pair-audit.json');q=load(E/'qualification.json');tag=q['tag'];i=load(E/(tag+'-input.json'));r=load(E/'receipts'/tag/'receipt.json')
assert r['exit_status']==10 and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
assert a['noncover_successes']==5513 and len(a['reached_covers'])==2
props=load(E/'case/properties-complete.json');assert len(props)==5515 and len({x['property'] for x in props})==5515
assert all(x['status']==('FAILURE' if x['property'] in a['reached_covers'] else 'SUCCESS') for x in props)
assert sha(E/'source/src/lib.rs')==i['source_sha256']==q['source_sha256']
h=i['harness_metadata'];assert h['attributes']['kind']=='Proof' and not h['attributes']['verified_stubs']
assert not any('AccountInfo' in str(x) or 'sdk_live_models' in str(x) or 'copy_from_slice' in str(x) or 'dealloc' in str(x) or 'Drop' in str(x) for x in h['attributes']['stubs'])
cg=load(E/'sdk-shared-prefix-codegen-success-bytes-pair-v1-input.json');assert '-C opt-level=3' in cg['env']['RUSTFLAGS']
for package,pin in cg['local_dependency_source_pins'].items():
 for rel,d in pin['files'].items():assert sha(E.parent/'sdk-native-first-pair/dependencies'/package/rel)==d
assert all(load(E/'sdk-shared-prefix-codegen-success-bytes-pair-v1-dependency-postcheck.json')['unchanged'].values())

def function(source,name):
 a=source.index('fn '+name+'(') if 'fn '+name+'(' in source else source.index('fn '+name+'<')
 b=source.index('{',a);depth=1;j=b+1
 while depth:
  depth+=(source[j]=='{')-(source[j]=='}');j+=1
 return source[a:j]
native=(E/'source/src/lib.rs').read_text();assert 'buffers[0][696]=2' not in native and 'vec![0;1768]' not in native
native=(E/'source/src/lib.rs').read_text();adapter=(R/'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text();program=(R/'programs/r1-cost-probe/src/lib.rs').read_text()
assert sha(R/'programs/r1-cost-probe/src/r1_pool_adapter.rs')=='6a8e5799035458ed4c0093709da6da86fb29100303861ddd15212d3ad7dcdcfb'
assert sha(R/'programs/r1-cost-probe/src/lib.rs')=='806264e5de0b54762872f72f129afad7c1ee5b71333c1a3375955dd8d6080172'
for name in ['stage1','readonly_buffer_meta_ok','require_readonly_buffer','require_verifier_checkpoint','require_distinct_accounts','decode_public_statement_box']:
 assert function(native,name)==function(adapter,name),name
for name in ['first_decoded','error']:assert function(native,name)==function(program,name),name
assert function(native,'observer')=='fn observer()->verifier::Observer {None}'
assert '#[cfg(not(feature="cu-profiling"))] {None}' in function(program,'observer')

with tempfile.TemporaryDirectory() as d:
 out=Path(d)/'source';subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-success-bytes-pair.py'),str(out)],check=True,stdout=subprocess.DEVNULL)
 for rel in ['src/lib.rs','Cargo.toml']:assert (out/rel).read_bytes()==(E/'source'/rel).read_bytes(),rel
print(json.dumps(dict(checks=5513,covers=2,scope=q['scope'],remaining=q['remaining']),indent=2))
