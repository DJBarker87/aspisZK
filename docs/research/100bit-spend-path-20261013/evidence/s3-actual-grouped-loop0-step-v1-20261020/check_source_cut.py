#!/usr/bin/env python3
"""Self-check the exact S3 v5 source cut and its Lean operations adaptation."""
from pathlib import Path
import hashlib, json, re, sys, tomllib
ROOT = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
def read(rel): return (ROOT / rel).read_bytes()
def require(cond, msg):
    if not cond: raise SystemExit('FAIL: ' + msg)
def norm(s): return re.sub(r'\s+', '', s.decode() if isinstance(s, bytes) else s)
# Frozen complete Rust files, pinned to the immutable repository revision.
rev='8137980396719c48f71f743254644aaf0a3a8423'
expected={
 'crates/aspis-r1-cost-probe/src/weights.rs':'30e8f10fa7f0adfe2101bb5df8bdfe0876ee70b35349ab886ab4dc30a0d16cca',
 'crates/aspis-core/src/field.rs':'28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea',
 'crates/aspis-core/src/field/wide_exact.rs':'6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b',
}
for p,h in expected.items(): require(sha(read('sources/rust-upstream/'+p))==h, 'frozen Rust source hash '+p)
weights=read('sources/rust-upstream/crates/aspis-r1-cost-probe/src/weights.rs')
start=weights.index(b'#[inline(never)]\nfn s2_grouped_inactive_pair(')
end=weights.index(b'\n}', start)+2
span=weights[start:end]
require((start,end)==(1140,1698), 'actual function byte range changed')
require(sha(span)=='7d21106ba48799416f1824e41964d5735155469c6358475794f89908cb5d6cb8', 'actual function span hash')
shim=read('sources/extraction-v5/input/lib.rs')
match=re.search(rb'#[\[]inline\(never\)\]\s*pub fn s2_grouped_inactive_pair\(.*?\n\}', shim, re.S)
require(match is not None, 'extraction shim helper not found')
actual_span=span.replace(b'\nfn s2_grouped_inactive_pair', b'\npub fn s2_grouped_inactive_pair')
require(norm(match.group(0))==norm(actual_span), 'shim helper does not match frozen source except pub visibility')
# Actual copied carrier declarations agree in shape with the frozen sources.
def rust_decl(buf, name):
    pat=rb'pub struct '+name.encode()+rb'\s*(?:\([^;]*\);|\{.*?\})'
    m=re.search(pat,buf,re.S)
    require(m is not None, 'missing Rust struct '+name)
    return m.group(0)
field=read('sources/rust-upstream/crates/aspis-core/src/field.rs')
wide=read('sources/rust-upstream/crates/aspis-core/src/field/wide_exact.rs')
for name in ('M31','CM31','QM31'):
    require(norm(rust_decl(field,name))==norm(rust_decl(shim,name)), 'carrier shape mismatch '+name)
require(norm(rust_decl(wide,'WideExact'))==norm(rust_decl(shim,'WideExact')), 'carrier shape mismatch WideExact')
require(norm(rust_decl(wide,'WideExact'))==norm(rust_decl(shim,'WideExact')), 'WideExact must retain both QM31 fields')
# LLBC metadata and Aeneas translation connect the captured snapshot to the emitted owner.
llbc=json.loads(read('sources/extraction-v5/S3GroupedPair.llbc'))
require(llbc.get('has_errors') is False, 'LLBC has errors')
require(llbc['translated']['crate_name']=='aspis_r1_current_powers', 'crate name mismatch')
trans=json.loads(read('sources/extraction-v5/generated/translation.json'))
require(trans['crate']=='aspis_r1_current_powers', 'Aeneas crate metadata mismatch')
fn=next((x for x in trans['functions'] if x.get('lean_name')=='AspisR1GroupedPairActualCut.weights.s2_grouped_inactive_pair'),None)
require(fn is not None and fn['rust_name']=='aspis_r1_current_powers::weights::s2_grouped_inactive_pair', 'generated function owner mismatch')
require(fn['source']=={'file':'lib.rs','begin_line':48,'end_line':63}, 'generated source span mismatch')
for name in ('M31','CM31','QM31','WideExact'):
    require(any(x.get('lean_name')=='AspisR1GroupedPairActualCut.field.'+name for x in trans['types']), 'missing translated carrier '+name)
# The output inputs really are the exact runner snapshots, but the old source-pins manifest is stale.
for phase in ('charon-a','aeneas-a'):
    base='attempts/actual-cut-v5/'+phase+'/'
    receipt=json.loads(read(base+'receipt.json'))
    command=json.loads(read(base+'command.json'))
    require(receipt['command']==command, phase+' command differs from receipt')
    require(receipt['outputs'].get('S3GroupedPair.llbc')=='27f4556d55790031e3b5eafa92154f1fdf2612f7ae75a453031ff7a1eb474779', phase+' LLBC receipt hash')
    require(receipt['source_revision']==rev and receipt['exit_status']==0, phase+' receipt success/revision')
    require(receipt['source_pins_sha256']=='658f1e663d1b327add266e4c56ae7927dbc78ad3f32b50a1e7c9ec0ad258c320', phase+' stale sidecar pin recorded accurately')
    require(receipt['process_swaps']==0 and receipt['cgroup_swap_current']==0, phase+' swap')
    require(receipt['limits']['memory.swap.max']=='0', phase+' swap cap')
charon=json.loads(read('attempts/actual-cut-v5/charon-a/command.json'))
require('--start-from' in charon and charon[charon.index('--start-from')+1]=='crate::weights::s2_grouped_inactive_pair', 'Charon root differs')
require(charon[charon.index('--dest-file')+1].endswith('/S3GroupedPair.llbc'), 'Charon output manifest path')
for opaque in ('crate::weights::field','crate::field::_::add','crate::field::_::mul'):
    require(charon.count('--opaque')==3 and opaque in charon, 'opaque cut missing '+opaque)
aeneas=json.loads(read('attempts/actual-cut-v5/aeneas-a/command.json'))
require('S3GroupedPair.llbc' in aeneas[-1] and aeneas[aeneas.index('-namespace')+1]=='AspisR1GroupedPairActualCut', 'Aeneas input/namespace mismatch')
for rel,h in [('generated/AspisR1GroupedPairActualCut/Funs.lean','1c08680cd1a0ceafb039e279b62f5f2ffcda7880b8068b4b938f42a6947b5aec'),('generated/AspisR1GroupedPairActualCut/Types.lean','7afc8eacea8f2e2dcbff734c3d98c0931faa4fb991e232906f26ca85efaa3370'),('generated/translation.json','1dd96d49073aa85d5e4c195e5dbd487d4858df67979a3a75af3b4eefa102532c')]:
    require(sha(read('sources/extraction-v5/'+rel))==h, 'Aeneas generated output hash '+rel)
for name in ('weights.field','field.WideExact.add','field.WideExact.mul'):
    item=next((x for x in trans['functions'] if x['lean_name'].endswith(name)),None)
    require(item is not None and item.get('is_opaque') is True, 'explicit opaque generated op '+name)
config=json.loads(read('sources/extraction-v5/config.json'))
require(config['unit']=='s3-grouped-pair-actual-cut-v5-20261020' and config['scope_memory_high_bytes']==1073741824 and config['scope_memory_max_bytes']==3221225472, 'extraction config identity/cap')
manifest=tomllib.loads(read('sources/extraction-v5/input/Cargo.toml').decode())
require(manifest['package']['name']=='aspis-r1-current-powers' and manifest['lib']['path']=='lib.rs', 'Cargo manifest identity/path')
for phase in ('charon-a','aeneas-a'):
    for name in ('Cargo.toml','Cargo.lock','lib.rs','source-pins.json'):
        a=read('sources/extraction-v5/input/'+name)
        b=read('sources/extraction-v5/runs/'+phase+'/input-snapshot/'+name)
        require(a==b, phase+' command input snapshot '+name)
runstage=read('sources/extraction-v5/run-stage.py').decode()
extract_host=read('sources/extraction-v5/extract-host.py').decode()
require('extract-host.py' in runstage and '--root' in runstage and 'w' in runstage, 'stage runner invokes extraction host')
require("kit=w/'input'" in extract_host and 'cwd=kit' in extract_host, 'runner Cargo working-directory/manifest path')
require(config['collector_sha256']=='4fc152ea4f88742fb460c301ae17446f1d1ba9162acdaafb37d80e60c4907800', 'collector pin in config')
runner=read('sources/extraction-v5/extract-host.py')
require(sha(runner)=='afba68b439dc054593fb6bc66567fccd4bffa860ba3e65f6429f83fab1375565', 'extraction runner pin')
collector=read('sources/extraction-v5/host-controller/collect-cgroups.py')
require(sha(collector)==config['collector_sha256'], 'host admission collector pin')
# This is a corrective audit, not an attempt to silently repair the original receipt.
oldpins=json.loads(read('sources/extraction-v5/input/source-pins.json'))
require(oldpins['source_cut']['path']=='crates/aspis-r1-cost-probe/src/weights.rs', 'old pin path unexpectedly changed')
require('pub fn s2_grouped_inactive_pair' in oldpins['source_cut']['function_text'], 'expected exported shim text in old pin')
require('powers' in oldpins['candidate_transform']['before'], 'expected unrelated powers candidate metadata not found')
require(sha(oldpins['source_cut']['function_text'].encode()) != sha(span), 'expected old function-text visibility mismatch')
require(sha(read('sources/extraction-v5/input/source-pins.json'))=='658f1e663d1b327add266e4c56ae7927dbc78ad3f32b50a1e7c9ec0ad258c320', 'old source-pins bytes changed')
# Exact reversible operations adapter: remove template import/option scopes, rename owner,
# and thread three explicit operations through the emitted body and its loop callers.
raw_types=read('sources/extraction-v5/generated/AspisR1GroupedPairActualCut/Types.lean').decode()
target_types=read('sources/actual/Types.lean').decode()
types=raw_types.replace('AspisR1GroupedPairActualCut','AspisR1GroupedPairActualFieldOpsV3')
types=re.sub(r'/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/\nset_option maxHeartbeats 1000000\n', '', types)
types=re.sub(r'/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/\nset_option maxRecDepth 2048\n', '', types)
types=types.replace('set_option linter.unusedVariables false\n\n\n\nnamespace ', 'set_option linter.unusedVariables false\n\n\nnamespace ')
# The selected type owner differs only by owner naming and removal of forbidden overrides.
require(types==target_types, 'raw generated Types → option-clean namespace owner transformation mismatch')
raw=read('sources/extraction-v5/generated/AspisR1GroupedPairActualCut/Funs.lean').decode()
target=read('sources/actual/Funs.lean').decode()
def replace_once(s,a,b):
    require(s.count(a)==1, 'adapter replacement count for '+repr(a))
    return s.replace(a,b,1)
s=raw
s=replace_once(s,'import AspisR1GroupedPairActualCut.Types\nimport AspisR1GroupedPairActualCut.FunsExternal','import AspisR1GroupedPairActualFieldOpsV3.Types')
s=s.replace('AspisR1GroupedPairActualCut','AspisR1GroupedPairActualFieldOpsV3')
s=re.sub(r'/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/\nset_option maxHeartbeats 1000000\n', '', s)
s=re.sub(r'/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/\nset_option maxRecDepth 2048\n', '', s)
s=replace_once(s,'namespace AspisR1GroupedPairActualFieldOpsV3\n','''namespace AspisR1GroupedPairActualFieldOpsV3

structure Operations where
  decodeField : Slice Std.U8 → Std.Usize → Result field.WideExact
  add : field.WideExact → field.WideExact → Result field.WideExact
  mul : field.WideExact → field.WideExact → Result field.WideExact
\n''')
threaded=(
 'weights.s2_grouped_inactive_pair_loop0.body',
 'weights.s2_grouped_inactive_pair_loop0',
 'weights.s2_grouped_inactive_pair_loop1_loop0.body',
 'weights.s2_grouped_inactive_pair_loop1_loop0',
 'weights.s2_grouped_inactive_pair_loop1.body',
 'weights.s2_grouped_inactive_pair_loop1',
 'weights.s2_grouped_inactive_pair',
)
for name in threaded:
    s=replace_once(s,'def '+name+'\n','def '+name+'\n  (ops : Operations)\n')
s=s.replace('weights.field f j','ops.decodeField f j')
s=s.replace('field.WideExact.add','ops.add').replace('field.WideExact.mul','ops.mul')
# Thread the operation record only at generated call sites, never def names.
for old,new in [
 ('=> weights.s2_grouped_inactive_pair_loop0.body\n','=> weights.s2_grouped_inactive_pair_loop0.body ops\n'),
 ('=> weights.s2_grouped_inactive_pair_loop1_loop0.body\n','=> weights.s2_grouped_inactive_pair_loop1_loop0.body ops\n'),
 ('weights.s2_grouped_inactive_pair_loop1_loop0 iter2 group','weights.s2_grouped_inactive_pair_loop1_loop0 ops iter2 group'),
 ('=> weights.s2_grouped_inactive_pair_loop1.body low','=> weights.s2_grouped_inactive_pair_loop1.body ops low'),
 ('weights.s2_grouped_inactive_pair_loop0\n      {','weights.s2_grouped_inactive_pair_loop0 ops\n      {'),
 ('weights.s2_grouped_inactive_pair_loop1\n    {','weights.s2_grouped_inactive_pair_loop1 ops\n    {'),
]: s=replace_once(s,old,new)
# Match the adapted file's single separator after removed resource-option blocks.
s=s.replace('set_option linter.unusedVariables false\n\n\n\n/- You can remove', 'set_option linter.unusedVariables false\n\n\n/- You can remove')
if s!=target:
    import difflib
    print('\n'.join(difflib.unified_diff(target.splitlines(),s.splitlines(),fromfile='target',tofile='computed',n=2)))
    require(False, 'raw generated Funs → explicit operations transformation mismatch')
for path in ('sources/actual/Funs.lean','sources/actual/Types.lean'):
    txt=read(path).decode()
    require('maxHeartbeats' not in txt and 'maxRecDepth' not in txt, 'resource option override present in adapted owner')

# Common packet schema, file hashes, direct-import map, and object receipts.
packet=json.loads(read('packet.json'))
require(packet.get('schema')=='focused-extractor-proof-packet-v1', 'packet schema')
for rel,h in packet['files'].items():
    require(sha(read(rel))==h, 'packet file hash '+rel)
    require(Path(rel).suffix not in ('.olean','.ir','.exe','.rlib','.a','.so','.dylib','.tar','.gz'), 'compiled artifact in packet '+rel)
require(packet['source_cut_checker_sha256']==sha(read('check_source_cut.py')), 'checker pin in packet')
for module in packet['proof_modules']:
    require(sha(read(module['source_path']))==module['source_sha256'], 'proof module source hash '+module['module'])
    receipt=json.loads(read(module['receipt_path']))
    preflight=json.loads(read(module['preflight_path']))
    require(receipt['exit_status']==0 and receipt['object_sha256']==module['object_sha256'], 'object receipt '+module['module'])
    require(preflight['source_sha256']==module['source_sha256'], 'preflight source '+module['module'])
    require(set(module['axioms'])=={'propext','Classical.choice','Quot.sound'}, 'standard axiom audit '+module['module'])
    for owner,entry in module['direct_imports'].items():
        require(entry['source_path'] is not None, 'direct import source path '+owner)
        require(sha(read(entry['source_path']))==entry['source_sha256'], 'direct import source hash '+owner)

# Repository-standard entrypoint; it is independently self-contained and
# maps each proof owner to its exact receipt/compiler/resource/audit record.
standard=json.loads(read('manifest.json'))
require(standard.get('schema')=='focused-extractor-proof-packet-v1', 'standard manifest schema')
require(standard.get('packet_id')==packet['packet_id'], 'standard manifest packet id')
require(len(standard.get('modules',[]))==len(packet['proof_modules']) and bool(standard.get('modules')), 'standard manifest modules')
require(bool(standard.get('direct_import_source_map')), 'standard direct import source map')
for rel,h in standard['files'].items():
    require(sha(read(rel))==h, 'standard manifest file hash '+rel)
for m in standard['modules']:
    require(sha(read(m['source']))==m['source_sha256'], 'standard module source '+m['module'])
    require(sha(read(m['receipt']))==m['receipt_sha256'], 'standard module receipt '+m['module'])
    require(m['exit_status']==0 and m['object_sha256'] and m['compiler_sha256'], 'standard module result/compiler '+m['module'])
    require(m['resource_caps'] and m['resource_caps'].get('memory.swap.max')=='0', 'standard module resource caps '+m['module'])
    require(set(m['axioms'])=={'propext','Classical.choice','Quot.sound'}, 'standard module axioms '+m['module'])
    require(bool(m['direct_imports']), 'standard module direct imports '+m['module'])
for owner,entry in standard['direct_import_source_map'].items():
    require(entry['source_path'] is not None, 'standard direct import source '+owner)
    require(sha(read(entry['source_path']))==entry['source_sha256'], 'standard direct import hash '+owner)
require(len(standard.get('owner_producers',[]))==2, 'selected generated owner producer records')
for producer in standard['owner_producers']:
    require(sha(read(producer['source']))==producer['source_sha256'], 'producer source '+producer['module'])
    require(sha(read(producer['receipt']))==producer['receipt_sha256'], 'producer receipt '+producer['module'])
    receipt=json.loads(read(producer['receipt']))
    preflight=json.loads(read(producer['preflight']))
    require(receipt['exit_status']==0 and receipt['object_sha256']==producer['object_sha256'], 'producer object '+producer['module'])
    require(preflight['source_sha256']==producer['source_sha256'], 'producer preflight source '+producer['module'])
    require(producer['resource_caps'].get('memory.swap.max')=='0', 'producer swap cap '+producer['module'])
    require(producer['scope_peak_bytes'] is not None and producer['swap_peak_bytes']==0, 'producer resource receipt '+producer['module'])

print('PASS: frozen source cut, actual 8-limb carrier, runner inputs/outputs, LLBC/Aeneas mapping, exact Lean adaptation, packet/source/import/object hashes, and standard axiom audits')
print('NOTE: original v5 receipt source_pins_sha256 binds a stale powers manifest; see provenance-correction.json')
