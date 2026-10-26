#!/usr/bin/env python3
"""Audit the actual Rust/extracted source/Nat/snapshot-helper chain."""
from pathlib import Path
import hashlib,json,re
import subprocess
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021'
O=E/'s6-bump-reference-extraction-v1'
S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
scope=load(O/'scope.json')
manifest=load(O/'manifest.json')
assert set(manifest['files'])=={str(p.relative_to(O))for p in O.rglob('*')if p.is_file()and p.name!='manifest.json'}
for path,pin in manifest['files'].items():assert sha(O/path)==pin,path
for path,pin in manifest['tool_source_pins'].items():assert sha(R/path)==pin,path
assert (O/'reviewed-source/S6StdOptionSourceV1.lean').read_bytes()==(S/'S6StdOptionSourceV1.lean').read_bytes()
assert (O/'reviewed-research/RELEASE-LEDGER-20261025.md').read_bytes()==subprocess.check_output(
 ['git','show',scope['research_revision']+':design/RELEASE-LEDGER-20261025.md'],cwd=R)
rust=(R/'tools/s6-bump-step-20261026/proof.rs').read_text()
begin=rust.index('pub fn step(');brace=rust.index('{',begin);end=brace+1;depth=1
while depth:depth+=(rust[end]=='{')-(rust[end]=='}');end+=1
body=rust[begin:end]
assert (O/'input/src/lib.rs').read_text()==body+'\n'
assert hashlib.sha256(body.encode()).hexdigest()==load(O/'binding.json')['body_sha256']
native=load(E/'s6-bump-step-terminal-v1/manifest.json')
assert body in (E/'s6-bump-step-terminal-v1'/native['source_workspace']/'harness/src/lib.rs').read_text()
positive=load(E/native['positive']/'receipt.json')
assert positive['exit_status']==0 and positive['source_unchanged']and positive['tools_unchanged']

charon=load(O/'run-charon/receipt.json');ci=load(O/'run-charon/input.json')
aeneas=load(O/'run-aeneas/receipt.json');ai=load(O/'run-aeneas/input.json')
assert charon['exit_status']==aeneas['exit_status']==0
assert charon['llbc_sha256']==aeneas['llbc_sha256']==ai['llbc_sha256']==load(O/'source-export/extraction.json')['llbc_sha256']
for phase,receipt,inputs,runner in [('charon',charon,ci,'nuc.py.v2'),('aeneas',aeneas,ai,'nuc.py')]:
 assert receipt['swaps']==0 and receipt['source_unchanged']and receipt['tools_unchanged']
 assert receipt['cgroup']['memory.swap.max']=='0'
 for kind in ['high','max','oom','oom_kill']:assert re.search(r'^'+kind+r' 0$',receipt['cgroup']['memory.events'],re.M)
 for name,pin in inputs['source_pins'].items():assert sha(O/(runner if name=='nuc.py'else name))==pin,(phase,name)
 for name in ['input/src/lib.rs','input/Cargo.toml','input/Cargo.lock']:assert ci['source_pins'][name]==ai['source_pins'][name]
 admission=load(O/('run-'+phase)/'admission-before-scope.json')
 assert admission['admitted'] and admission['finite_reserved_bytes']+admission['additional_bytes']<admission['limit_bytes']
 assert load(O/('run-'+phase)/'admission-in-scope.json')['admitted']
assert charon['cgroup']['memory.max']==str(2**30)
assert aeneas['cgroup']['memory.max']==str(512*2**20)

normal=load(O/'normalization.json');raw=(O/'source-export/raw-Funs.lean.txt').read_text()
assert hashlib.sha256(raw.encode()).hexdigest()==normal['raw_source_sha256']
for before,after in normal['rewrites'].items():
 assert raw.count(before)==1
 raw=raw.replace(before,after)
raw+='\n'+'\n'.join('#print axioms '+name for name in normal['appended_axioms_reports'])+'\n'
assert (S/'S6BumpOwnedReferenceSourceV1.lean').read_text()==raw
assert sha(S/'S6BumpOwnedReferenceSourceV1.lean')==normal['normalized_source_sha256']
info=load(O/'source-export/target-info.json')
assert info==[{'key':'x86_64-unknown-linux-gnu','value':{'target_pointer_size':8,'is_little_endian':True}}]
assert 'def core.option.Option.Insts.CoreOpsTry_traitTry.branch' in raw
assert 'core.mem.size_of'not in raw and 'FunsExternal'not in raw

targets={'S6BumpOwnedReferenceSourceV1':'s6-bump-reference-source-v2',
 'S6BumpReferenceExactV1':'s6-bump-reference-exact-v2',
 'S6BumpReferenceReserveV1':'s6-bump-reference-reserve-v2',
 'S6SnapshotSourceAllocatorV1':'s6-snapshot-source-allocator-v3'}
reports=0
for name,attempt in targets.items():
 a=E/attempt;r=load(a/'receipt.json')
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert '-j1'in r['command']and'-M4400'in r['command']
 assert sha(S/(name+'.lean'))==sha(a/'source.lean')==r['source_sha256']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',(S/(name+'.lean')).read_text(),re.M)
 for report in r['print_axioms']:
  if 'does not depend on any axioms'in report:reports+=1;continue
  match=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
  assert match and set(re.findall(r'[A-Za-z_.]+',match[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
for failed in ['s6-bump-reference-source-v1','s6-bump-reference-exact-v1',
               's6-bump-reference-reserve-v1','s6-snapshot-source-allocator-v1','s6-snapshot-source-allocator-v2']:
 assert load(E/failed/'receipt.json')['exit_status']!=0
for path in O.rglob('*'):
 if path.is_file():assert path.suffix in ['.json','.log','.rs','.toml','.lock','.txt','.py','.v1','.v2','.lean','.md'],path
print(json.dumps({'status':'PASS','targets':len(targets),'standard_axiom_reports':reports,
 'same_native_checked_rust_reference_extracted':True,'complete_owned_step_total_exact':True,
 'finite_emitted_step_sequence_total_exact':True,'original_snapshot_helper_concrete_reference_total':True,
 'whole_native_entry_heap_admission_proved':False,'concrete_sdk_stage1_binding_proved':False,
 'enclosing_source_trust_premises_removed':0,'whole_s6_closed':False}))
