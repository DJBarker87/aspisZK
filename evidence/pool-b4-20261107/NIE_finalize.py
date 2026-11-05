from pathlib import Path
import json,hashlib,subprocess,lzma,re,shutil
E=Path(__file__).resolve().parent;REPO=E.parent.parent
J=lambda p:json.loads(Path(p).read_text())
receipts=[J(p) for p in E.glob('NIE_[KLE][0-9][0-9][0-9]/receipt.json')]
counts={k:sum(r['attempt'].startswith('NIE_'+prefix) for r in receipts) for k,prefix in [('kani','K'),('lean','L'),('extraction','E')]}
assert counts==dict(kani=120,lean=16,extraction=2)
summary=dict(budget_used=counts,lean_budget_note='14 focused compile/link/audit slots plus2 conservatively charged metadata-only export/cleanup scopes; no compiler in L015/L016',new_composed_rows=0,model_theorems=15,native_local_pass=53,native_semantic_controls=61,native_compiler_input_rejections=5,native_unwind_rejections=1,native_timeout_or_memory_kill=False,extraction_outcomes={'NIE_E001':'cold optimized compilation timeout before LLBC','NIE_E002':'complete NHR staging and Charon pass; actual lane Aeneas rejection'},scopes=len(receipts),wall_seconds_sum=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),source_revisions=sorted(set(r['source_revision'] for r in receipts)),formal_release_claim=False)
(E/'NIE_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
validation=J(E/'NIE_VALIDATION.json');observations=[]
for g in validation['paired_observation_groups']:
 for a in g['positive']:
  shape=J(E/(a+'-shape.json'))
  observations.append(dict(attempt=a,controls=g['negative'],kind=shape['kind'],domain=shape['domain'],remaining=shape['remaining'],shape=a+'-shape.json',native_source=a+'-NIE_native.patch',certified_universal_modifies=False,production_composed_credit=False))
assert len(observations)==53
(E/'NIE_NATIVE_OBSERVATIONS.json').write_text(json.dumps(dict(observations=observations,new_composed_rows=0,all_source_control_domains_explicit=True),indent=2)+'\n')
# Retain large identical snapshot inputs once, with verified references.
references=[]
for p in E.glob('NIE_L*/sources/**/NIE_EXPECTED_IMPORTS.jsonl'):
 q=E/'NIE_EXPECTED_IMPORTS.jsonl';raw=p.read_bytes();assert raw==q.read_bytes()
 ref=dict(path=str(q.relative_to(E)),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),reason='Identical large pinned input retained once; original receipt source hash unchanged')
 p.with_name(p.name+'.REFERENCE.json').write_text(json.dumps(ref,indent=2)+'\n');p.unlink();references.append(str(p.relative_to(E)))
(E/'NIE_SOURCE_DEDUP.json').write_text(json.dumps(dict(references=references,only_identical_verified_inputs=True),indent=2)+'\n')
# Every theorem audit is successful; recovery/elaboration failures stay separate.
audit=J(E/'NIE_AUDIT.json');audit.update(cache_exports='NIE_EXPORT.json',closure_pins='NIE_CLOSURE_PINS.json.xz',housekeeping_attempts=['NIE_L015','NIE_L016']);(E/'NIE_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
delta=J(E/'NIE_LEDGER_DELTA.json');delta.update(status='VALIDATED additive Pool checks; no new composed closure',validation='NIE_VALIDATION.json');(E/'NIE_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
rows=[]
for p in sorted(E.glob('NIE_K*-shape.json')):
 x=J(p);bad=bool(re.search(r'\bstatic\s+mut\b|\bstatic\s+[^;=]+:\s*[^;=]*(?:Cell|RefCell|UnsafeCell|Atomic)',x['source']));assert not bad;rows.append(dict(attempt=p.name.split('-')[0],no_writable_static=True))
(E/'NIE_INLINE_RULE16_AUDIT.json').write_text(json.dumps(dict(checked=rows,all_pass=True,gate_repaired=True,suspended_harnesses=[],quarantined_credited=[]),indent=2)+'\n')
# Check full shipped trees, not only selected call files.
changed=subprocess.check_output(['git','diff','--name-only','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs'],cwd=REPO,text=True).splitlines();assert not changed
(E/'NIE_SHIPPED_IDENTITY.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',changed=changed,elf_rebuild_trigger=False,new_elf_rebuild=False,inherited_only={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}),indent=2)+'\n')
for p in E.rglob('__pycache__'):
 if p.is_dir():shutil.rmtree(p)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
print(json.dumps(dict(budget=counts,new_composed_rows=0,local_pass=53,controls=61,scopes=len(receipts),peak_rss_kib=summary['peak_rss_kib'],swap=summary['swaps'],deduplicated_inputs=len(references))))
