#!/usr/bin/env python3
"""Audit template-free sampler extraction and exact outer control flow.
Explicitly retains the inherited opaque Formatter type dependency. This is
not a full inner-sampler, trace-refinement or privacy release gate.
"""
import argparse, hashlib, json, re, subprocess, sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r72-sampler';sel=e/'selected';parent=root/'evidence/r71-circle'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def read(f):return json.loads(f.read_text())
def metrics(f,code=0):
    s=f.read_text();assert re.findall(r'\tExit status: (\d+)',s)==[str(code)]
    assert re.findall(r'\tSwaps: (\d+)',s)==['0']
    wall=re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[0]
    return {'exit':code,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(wall.split(':')))),2),
        'peak_rss_kib':int(re.findall(r'Maximum resident set size \(kbytes\): (\d+)',s)[0])}
subprocess.run([sys.executable,str(root/'tools/check_r71_evidence.py')],check=True)
subprocess.run([sys.executable,str(root/'tools/stage_r72_sampler.py'),
    str(sel/'generated/AspisR72Sampler'),str(root/'lean'),'--check'],check=True)
base='bc92dd5675b58ba3076b999429f7cbdfc6675baf'
pins=read(sel/'source-pins.json');assert pins['base_revision']==base
stage=read(sel/'r18-stage.json');assert len(stage['files'])==202
assert sha(sel/'r18-stage.json')==pins['stage_manifest_sha256']==sha(root/'evidence/r69-explicit-source/runtime/r18-stage.json')
for rel,h in pins['unchanged_source_files'].items():
    assert h==stage['files']['crates/aspis-core/src/'+rel]
    src=sel/'source/src'/rel
    if rel=='lib.rs':
        data=src.read_text();assert data.endswith(pins['lib_append'])
        assert hashlib.sha256(data[:-len(pins['lib_append'])].encode()).hexdigest()==h
        assert sha(src)==pins['extraction_lib_sha256']
    else:assert sha(src)==h,rel
assert pins['build_sha256']==sha(sel/'source/build.rs')==sha(repo/'crates/aspis-core/build.rs')
assert sha(sel/'source/Cargo.toml')==pins['cargo_sha256']
assert pins['charon_sha256']=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
assert pins['aeneas_sha256']=='e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813'
commands=read(sel/'commands.json');assert [c['exit']for c in commands]==[0,0,0]
for flag in ['--release','--locked','--offline','core::result::_::map_err','core::option']:
    assert flag in commands[1]['command']
assert read(sel/'environment.json')['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
assert not read(sel/'R72Sampler.llbc')['has_errors']
meta=read(sel/'generated/translation.json')
assert len(meta['functions'])==49 and len(meta['types'])==10
assert not any(f['is_opaque']for f in meta['functions'])
for n,h in read(sel/'generated-pins.json').items():assert sha(sel/n)==h,n
assert [c['exit']for c in read(e/'missing-build/commands.json')]==[0,101]
assert [c['exit']for c in read(e/'opaque-map-err/commands.json')]==[0,0,0]
assert [c['exit']for c in read(e/'broad-result/commands.json')]==[0,0,2]
assert 'Not allowed to expand enumerations with several variants' in (e/'broad-result/translate.log').read_text()
template=(e/'opaque-map-err/generated/AspisR72Sampler/FunsExternal_Template.lean').read_text()
assert 'axiom core.result.Result.map_err' in template
records=read(e/'final/metadata.json');assert len(records)==322
assert records[:319]==read(parent/'final/metadata.json')
targets=['AspisR72Sampler/Types','AspisR72Sampler/Funs','AspisV8R19/SamplerOuterExecution']
assert [r['target_name']for r in records[-3:]]==targets
logs={label:metrics(sel/(label+'.log'))for label in ['lock','extract','translate']}
for r in records[-3:]:
    name=r['target_name'];src=root/'lean'/(name+'.lean')
    assert r['source_sha256']==sha(src) and r['base_revision']==base and r['exit']==0
    assert r['toolchain']=='leanprover/lean4:v4.32.0'
    assert not re.search(r'\b(axiom|sorry|admit)\b',src.read_text())
    logs[name]=metrics(e/'final'/(Path(name).name+'.log'))
deps=read(e/'final/dependency-pins.json');assert len(deps)==283
assert read(e/'collection.json')['dependency_pins_verified']==283
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker,1)[1])==h,path
fmtpath=next(path for path in deps if path.endswith('/Aeneas/Std/Core/Fmt.lean'))
assert sha(e/'runtime/CoreFmt.lean')==deps[fmtpath]
fmt=(e/'runtime/CoreFmt.lean').read_text()
assert 'axiom core.fmt.Formatter : Type' in fmt
assert '(_ : core.fmt.Debug E)' in fmt and '| .Err _ => .fail .panic' in fmt
log=(e/'final/SamplerOuterExecution.log').read_text();assert 'sorryAx' not in log
audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
assert len(audits)==14
opaque_users=[]
for name,axs in audits:
    aset={x.strip()for x in axs.split(',')if x.strip()}
    assert aset<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter'}
    if 'core.fmt.Formatter'in aset:opaque_users.append(name)
assert len(opaque_users)==11
for folder in ['final','selected','missing-build','opaque-map-err','broad-result']:
    res=read(e/folder/'resources.json')
    assert {k:res[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']}=={
        'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'}
receipt={'base_revision':base,'new_theorems':11,'generated_definition_audits':3,
    'compiled_targets':3,'cached_targets':319,'logs':logs,'extracted_functions':49,
    'opaque_extracted_functions':0,'external_templates':0,'new_axiom_declarations':0,
    'inherited_opaque_runtime_type':'core.fmt.Formatter : Type','opaque_type_users':opaque_users,
    'standard_axioms_only':False,'source_outer_loop_equivalence':True,
    'source_inner_sampler_correspondence':False,'source_shared_oracle_trace_correspondence':False,
    'runtime_changed':False,'cu':[1495663,1497050],'actual_1M_gate_passed':False,
    'full_privacy':False,'full_soundness':False,
    'first_remaining':'Prove the generated squeeze/byte/limb sampler against the retained memoized shared-oracle program, including safe four-byte slicing, little-endian decoding, P rejection, block rollover, eight-attempt bounds and state/trace observations; transport R71 circle semantics to the R72 namespace.'}
files=[root/'lean'/(t+'.lean')for t in targets]
files += [root/'tools'/n for n in ['check_r72_evidence.py','collect_r72_evidence.py','extract_r72_sampler.py',
    'stage_r72_sampler.py','run_r72_lean.py','run_r68_lean.py','run_r64_lean.py','run_r63_lean.py']]
files += [parent/'MANIFEST.json',parent/'receipt.json',repo/'crates/aspis-core/build.rs']
sourcepins={str(f.relative_to(repo)):sha(f)for f in files}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(sourcepins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert read(e/'receipt.json')==receipt and read(e/'SOURCE_PINS.json')==sourcepins
manifest=read(e/'MANIFEST.json')
assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'audit':'PASS_SCOPED','theorems':11,'inherited_opaque_type':'core.fmt.Formatter',
    'full_privacy':False,'artifacts':len(manifest),'logs':logs},indent=2))
