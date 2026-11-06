from pathlib import Path
import json,lzma,hashlib,subprocess,re
E=Path(__file__).resolve().parent;standard={'propext','Classical.choice','Quot.sound'}
receipts=[json.loads(p.read_text()) for p in E.glob('NLC_[LK][0-9][0-9][0-9]/receipt.json')]
assert {x['attempt'] for x in receipts if x['attempt'].startswith('NLC_L')}=={f'NLC_L{i:03}'for i in range(1,151)}
assert {x['attempt'] for x in receipts if x['attempt'].startswith('NLC_K')}=={f'NLC_K{i:03}'for i in range(1,21)}
manifest=json.loads((E/'NLC_AUDIT_ROOTS.json').read_text());results=[];disagreements=[]
for i in range(len(manifest['groups'])):
 p=E/'NLC_audit'/f'proof{i}'/f'proof{i}.json';x=json.loads(p.read_text());results+=x['results']
 for r in x['results']:
  assert set(r['walked_axioms'])<=standard,r
  if not r.get('equal',True):disagreements.append(r)
assert set(x['root'] for x in results)==set(manifest['roots'])
assert all(x['root']=='NHC_DecodeModel.decoder_error'for x in disagreements)
scan=[json.loads(l)for l in(E/'NLC_LOADED_scan.jsonl').read_text().splitlines()];assert all(not x['dangling']and not x['duplicate_owners']and x['imports_match']for x in scan)
fixture=json.loads((E/'NLC_audit/fixtures/fixtures.json').read_text());assert fixture['exit_status']==0 and len(fixture['results'])==8
prior=json.loads((E/'NLC_PREDECESSOR_COMPARISON.json').read_text());assert all(x['status']=='PASS'for x in prior.values())
assert json.loads((E/'NLC_FINAL_PINS.json').read_text())['unchanged']
for x in receipts:
 assert str(x['swaps'])=='0',x
 # Per-scope source revisions, hashes, dependency fingerprints and axiom lines remain in full receipts.
metrics=dict(scopes=len(receipts),lean_support_used=150,lean_support_budget=150,kani_used=20,kani_budget=20,extraction=0,peak_rss_kib=max(int(x['peak_rss_kib'])for x in receipts),swaps=0,total_wall_seconds=sum(float(x['wall_seconds'])for x in receipts),by_kind={k:sum(x['kind']==k for x in receipts)for k in sorted({x['kind']for x in receipts})})
out=dict(status='VALIDATED support only; target not yet established',headline='AspisR1.RPx_Deployed.deployed',row_delta=0,row_roots=[],parameterized_native_folds=[],source_interpreter_only=True,full_combined_audits=1,combined_attempt='NLC_L110',combined_exit=0,scan_attempt='NLC_L116',scan_exit=0,modules=len(scan),dangling=0,conflicting_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(x.get('cached_replicas',[]))for x in scan),required_raw_roots=len(set(manifest['roots'])),raw_result_count=len(results),raw_standard_axioms_only=True,collect_axioms_disagreements=disagreements,raw_authority="(ab')(3)/(ax2)",fixtures=fixture['results'],predecessor_comparison=prior,resources=metrics,native=json.loads((E/'NLC_NATIVE_RESULTS.json').read_text()),native_source_review=json.loads((E/'NLC_NATIVE_SOURCE_REVIEW.json').read_text()),export=json.loads((E/'NLC_EXPORT.json').read_text()),host_final=json.loads((E/'NLC_HOST_FINAL.json').read_text()),final_pins=json.loads((E/'NLC_FINAL_PINS.json').read_text()),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),cold_release_replay=False,new_trust_rows=[],pending_trust_used=[],shipped_source_changes=False,source_to_elf_rebuild=False,target_established=False)
(E/'NLC_AUDIT.json').write_text(json.dumps(out,indent=2))
(E/'NLC_STATEMENTS.txt').write_text((E/'NLC_L110/stdout.log').read_text())
for p in E.rglob('*'):
 if p.is_file() and p.stat().st_size>20_000_000:raise RuntimeError('Oversized evidence: '+str(p))
print(json.dumps(dict(status='SUPPORT_GATE_PASS_NO_ROW_CREDIT',raw_roots=out['required_raw_roots'],modules=len(scan),budgets='150/150 Lean-support;20/20 Kani;0 extraction',peak_rss_kib=metrics['peak_rss_kib'],row_delta=0)))
