from pathlib import Path
import json,lzma,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2-20261028'
rows=['V229','V230','V231','V238','V239','V240','V247','V256','V257','V258','V259']
suites=['rows','arithmetic','sha','ct','multilinear','leaves','sum','sampler','sampler','weights','weights']
for row,suite in zip(rows,suites):
 prior=json.loads((E/(row+'-prior.json')).read_text());g=json.loads(lzma.decompress((E/(row+'-source-gate.json.xz')).read_bytes()));native=E/('native-'+suite)/'receipt.json';nr=json.loads(native.read_text());assert nr['exit']==0
 known=[dict(function=f['function'],source_class=f.get('source_class'),diff=f.get('diff'),source_evidence=f.get('source_evidence')) for f in prior['per_function'] if f.get('source_class') in ['B','C'] and f.get('diff')]
 assert known
 first=known[0]['function']
 project='Original standalone complete project checker not recovered/rebound; the deployed source guard is partial, and does not replace that checker.'
 if row=='V229':project='Original project-only checker recovered and passed (V229-project-check.json), including exact body copies and fixed schedule certificates. The script display bug was omitted without changing its checks. No historical receipt acceptance or --finalize was run.'
 if row in ['V231','V238']:project='Original wrapper checker re-run on the deployed dependencies: PASS (wrapper-structural/results.json). This retains the explicit parametric finalizer/compression boundary; it is not a proof of all std descendants.'
 reason=f'No complete deployed-body law/source binding for {first}. The live1.94.1 source differs from the historical item. The padded-layout model lemma supplies only a natural-number transport on already-padded sizes, not a native Layout/pointer/allocator proof. Other exact changed-source obligations and unresolved instantiations/call targets are retained in {row}-source-gate.json.xz.'
 if row in ['V231','V238','V240','V247','V256','V257','V258']:
  reason=f'No complete deployed NonNull pointer-construction/cast law linked to the original model (first changed source: {first}). A source hash and matching values on finite inputs do not prove provenance, borrow restoration or full Result correspondence. Other exact source obligations and unresolved instantiations/call targets are retained in {row}-source-gate.json.xz.'
 j=dict(row=row,name=prior['name'],disposition='SUSPENDED',class_='B',native_link_evidence_class='finite validation; structural transfer incomplete, no restored credit',deployed_native_receipt=str(native.relative_to(E)),native_profile=nr['profile'],toolchain=nr['toolchain'],resolved_features_in_receipt=True,project_structural=project,exact_reason=reason,known_changed_functions=known,partial_guard=str((E/(row+'-source-gate.json.xz')).relative_to(E)),unresolved_source_associations=g['unresolved_source_associations'],prior_conservative_mir_residuals=prior['residuals'],before='Native association SUSPENDED by D386; Lean/model source laws retained.',after='Native association remains SUSPENDED; finite deployed validation refreshed; no claim that the native law is false.',premises=dict(removed=0,added=0,changed=0,trust=['entropy_law','entropy_kernel','observation']),finding=False,kani_runs=0,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
 (E/(row+'.json')).write_text(json.dumps(j,indent=2)+'\n')
 (E/(row+'.md')).write_text(f'''# {row}: SUSPENDED — class B\n\n{prior['name']}\n\n{reason}\n\n{project}\n\nDeployed finite native validation: [{suite} receipt](native-{suite}/receipt.json), exit0; rustc1.94.1 release, assertions/overflow checks off. Every resolved crate feature list is in that receipt, backed by compressed cargo metadata and input/source pins. This run validates its recorded finite inputs only. No Kani credit or SBF/ELF correspondence is claimed.\n\nThe full retained changed-function list, before/after source spans, and exact unresolved source associations are in [{row}.json]({row}.json) and the compressed source-gate result. Old source identity rejection is not a behavioural counterexample. No FINDING against native values was observed.\n\nBefore: deployed native link suspended; existing Lean/model laws retained. After: same status with new configuration-specific evidence. Endpoint premises removed0/added0/changed0; E1/E2, real RunJoin, client route, L1/L2/L3 and exactly the existing three trust fields remain. No simulator/observer change.\n\nNext: establish the named deployed std body laws and concrete call/instantiation boundary; recover/rebind any remaining project source checker; then replay this row's actual law/installation cone with an axioms audit before restoration.\n''')
 paths=[E/(row+'-prior.json'),E/(row+'-source-gate.json.xz'),E/(row+'-source-gate.sha256'),E/(row+'.json'),E/(row+'.md')]
 # Commit each shared native receipt only on its first consuming row.
 if row not in ['V257','V259']:
  paths += [native.parent];driver=E/('native-'+suite+'-driver.log')
  if driver.exists():paths.append(driver)
 if row=='V229':paths += [E/'V229-project-check.json',E/'V229-project-check.log']
 subprocess.run(['git','add','--',*[str(p.relative_to(R)) for p in paths]],cwd=R,check=True)
 assert not list(E.rglob('*20M-never*'))
 subprocess.run(['git','commit','-m',f'Record {row} deployed validation and exact suspension'],cwd=R,check=True)
 print(row,'SUSPENDED',flush=True)
