#!/usr/bin/env python3
"""Audit source-step and finite-control packets, without unchanged replay."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-claim-source-steps';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(P/'manifest.json');assert set(m['files'])=={str(p.relative_to(P)) for p in P.rglob('*') if p.is_file()}-{'manifest.json'}
for rel,d in m['files'].items():assert sha(P/rel)==d,rel
assert not any(p.suffix in ['.olean','.o','.exe','.out','.rlib','.llbc','.pyc'] for p in P.rglob('*'))
final='s1-claim-step-coupled-strict-v3';A=P/'attempts'/final;r=load(A/'receipt.json');i=load(A/'input.json');assert r['exit_status']==0 and r['swaps']==0
assert r['limits']['memory.swap.max']=='0' and r['limits']['memory.max']=='8589934592' and r['limits']['memory.high']=='6442450944'
assert '-Z mir-opt-level=0' in i['env']['RUSTFLAGS'] and '-C opt-level=3' in i['env']['RUSTFLAGS']
log=(A/'stdout.log').read_text();assert '0 of 789 failed' in log and '3 of 3 cover properties satisfied' in log
for rel,d in i['crate_source_pins'].items():assert sha(P/'inputs/v12'/rel)==d,rel
assert sha(P/'inputs/v12/Cargo.lock')==i['cargo_lock_sha256']
before=load(A/'all-local-before.json')['dependencies'];after=load(A/'all-local-after.json')['unchanged'];assert before.keys()==after.keys() and all(after.values())
for name,row in before.items():
 if row['root'].endswith('aspis-s1-claim-source-steps-v12'):
  for rel,d in row['files'].items():
   p=P/'dependency/frozen-probe'/rel.removeprefix('frozen-probe/') if rel.startswith('frozen-probe/') else P/'inputs/v12'/rel
   assert sha(p)==d,rel
 if row['root'].endswith('frozen-probe'):
  for rel,d in row['files'].items():assert sha(P/'dependency/frozen-probe'/rel)==d,rel
binding=load(P/'inputs/v12/source-binding.json');rev=binding['revision'];path='crates/aspis-r1-cost-probe/src/'
for name,d in binding['source_files'].items():
 raw=subprocess.check_output(['git','-C',str(R),'show',rev+':'+path+name]);assert hashlib.sha256(raw).hexdigest()==d,name
 assert sha(P/'dependency/frozen-probe/src'/name)==d,name
source=(P/'inputs/v12/src/lib.rs').read_text();assert binding['original_claim'] in source and binding['selector'] in source and binding['steps'] in source
assert 'dot.push(g[l],scalar).map_err(|_|Error::Parse)?;' in binding['steps']
assert sha(P/'inputs/v12/src/fast_pairing.rs')==binding['source_files']['fast_pairing.rs']
proof=(P/'inputs/v12/src/proofs.rs').read_text();assert 'kani::assume(point<6&&l<29)' in proof
assert '#[kani::stub(fast_pairing::EbyKDot::push,coupled_push)]' in proof
assert '#[kani::stub(aspis_r1_cost_probe::weights::field,coupled_field)]' in proof
assert 'assert_eq!(a,if error{Err(Error::Parse)}else{Ok(())});' in proof
# Same caller/source/harness, different MIR configuration: preserve the failed
# check and forbid presenting it as source equivalence or a shipped SDK bug.
failed=P/'attempts/s1-push-maperr-result-preflight-v1';fixed=P/'attempts/s1-push-maperr-mir0-v1'
assert load(failed/'receipt.json')['exit_status']!=0 and load(fixed/'receipt.json')['exit_status']==0
fi=load(failed/'input.json');mi=load(fixed/'input.json');assert fi['source_sha256']==mi['source_sha256'] and fi['crate_source_pins']==mi['crate_source_pins']
assert 'mir-opt-level=0' not in fi['env']['RUSTFLAGS'] and 'mir-opt-level=0' in mi['env']['RUSTFLAGS']
assert '2 of 2 cover properties satisfied' in (fixed/'stdout.log').read_text()
actual=P/'attempts/s1-claim-selector-actual-v1';assert load(actual/'receipt.json')['exit_status']==0
assert '0 of 927 failed' in (actual/'stdout.log').read_text() and '7 of 7 cover properties satisfied' in (actual/'stdout.log').read_text()
rows=[('S1ClaimDotBoundedResultV1','s1-claim-dot-bounded-result-v2'),('S1ClaimBoundedResultCompositionV1','s1-claim-bounded-result-compose-v3'),('S1ClaimAllLoopsBoundedV1','s1-claim-all-loops-bounded-v1')]
pins=load(E/'s1-claim-bounded-result-import-pins.json');accepted=load(E/'accepted-targets.json')['targets'];reports=0
for name,attempt in rows:
 r=load(E/attempt/'receipt.json');assert r['exit_status']==0 and r['swaps']==0
 assert sha(S/(name+'.lean'))==sha(E/attempt/'source.lean')==r['source_sha256']==accepted[name]['source_sha256']==pins['targets'][name]['source_sha256']
 assert r['object_sha256']==pins['targets'][name]['object_sha256'] and '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',(S/(name+'.lean')).read_text(),re.M)
 for report in r['print_axioms']:
  match=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert match and set(re.findall(r'[A-Za-z_.]+',match[1]))<={'propext','Classical.choice','Quot.sound'};reports+=1
assert reports==9
print(json.dumps(dict(source_step_checks=789,source_step_covers=3,actual_selector_checks=927,lean_standard_axiom_reports=reports,finite_inner_outer_control=True,full_reference_claim_result_preserved=True,all_local_path_dependencies=len(before),original_nested_source_refinement_closed=False,arithmetic_leaf_interpretation_closed=False,whole_s1_closed=False,whole_s6_closed=False)))
