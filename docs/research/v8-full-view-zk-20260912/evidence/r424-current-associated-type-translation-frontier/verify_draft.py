#!/usr/bin/env python3
"""Read-only checks for the R424 diagnostic draft; no builds or tests."""
import hashlib,json,pathlib,sys
root=pathlib.Path(__file__).resolve().parent
ev=root/'evidence'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((root/'bundle-manifest.json').read_text())
errors=[]
expected={row['bundle_path']:row['sha256'] for row in manifest['files']}
for rel,digest in expected.items():
 p=root/rel
 if not p.is_file(): errors.append('missing '+rel)
 elif sha(p)!=digest: errors.append('hash mismatch '+rel)
actual={str(p.relative_to(root)) for p in ev.rglob('*') if p.is_file()}
if actual!=set(expected): errors.append(f'evidence inventory differs: missing={sorted(set(expected)-actual)} extra={sorted(actual-set(expected))}')
# High-value phase checks from bundled receipts.
pre='evidence/build-preflight/'
def j(rel):return json.loads((root/rel).read_text())
for tag,status,boundary in [
 ('r424-fixture-build-v1',1,'Fixture executable compilation failed at the Map API call. No fixture executable was produced and no assertions ran.'),
 ('r424-fixture-build-v2',1,'Fixture executable compilation failed on the associated-item map type annotation. No fixture executable was produced and no assertions ran.'),
 ('r424-fixture-build-v3',0,'The focused ConcreteAssociatedTypesFixture executable compiled successfully. This build phase did not run fixture assertions.')]:
 receipt=j(pre+tag+'/metrics-receipt.json'); result=j(pre+tag+'/result.json')
 if receipt.get('exit_status')!=status or result.get('exit_status')!=status or receipt.get('proved_boundary')!=boundary: errors.append(tag+' phase/status mismatch')
execution=j(pre+'r424-fixture-execution-v1/receipt.json')
if execution.get('exit_status')!=0 or execution.get('assertions_passed')!=14 or execution.get('all_checks_passed') is not True: errors.append('execution receipt mismatch')
main=j(pre+'r424-main-build-v1/build-result.json')
if main.get('build_exit_status')!=0 or main.get('translation_or_Lean_run') is not False: errors.append('main build receipt mismatch')
tr=j('evidence/translation/output/a3fe5df6b53c-20261002T203426Z/translation-result.json')
if tr.get('translator_exit_status')!=2 or tr.get('generated_dir_exists') is not False or tr.get('manifest_function_entries')!=0: errors.append('translation failure receipt mismatch')
for p in [root/'R424_CURRENT_GAT_TRANSLATION_FRONTIER.md',root/'verify_draft.py']:
 if not p.is_file(): errors.append('missing '+p.name)
print(json.dumps({'result':'PASS' if not errors else 'FAIL','bundle_file_count':len(expected),'errors':errors,
 'boundary':'Receipt/source/hash consistency only; no compiler, fixture, translation, Lean, or semantic replay.'},indent=2))
sys.exit(0 if not errors else 1)
