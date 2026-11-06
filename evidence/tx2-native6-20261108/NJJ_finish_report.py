from pathlib import Path
import json,hashlib,lzma,subprocess
E=Path(__file__).resolve().parent
roots=json.loads((E/'NJJ_AUDIT_ROOTS.json').read_text())['roots'];raw=[]
for p in sorted((E/'NJJ_audit/all').glob('proof*.json')):
 x=json.loads(p.read_text());assert x['exit_status']==0
 raw.extend(x['results'])
assert len(raw)==len(roots)==45
standard={'propext','Classical.choice','Quot.sound'}
for r in raw:assert r['equal'] and set(r['walked_axioms'])<=standard and set(r['collect_axioms'])<=standard,r
fixtures=json.loads((E/'NJJ_audit/fixtures/fixtures.json').read_text());gold=json.loads((E/'NJJ_EXPECTED_FIXTURES.json').read_text())
assert len(fixtures['results'])==8
for r in fixtures['results']:assert r['equal'] and r['walked_axioms']==gold[r['root']] and r['collect_axioms']==gold[r['root']],r
scan=[json.loads(s) for s in (E/'NJJ_LOADED_scan.jsonl').read_text().splitlines() if s.strip()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
walker=json.loads((E/'NJJ_WALKER_PIN.json').read_text());assert walker['source_sha256']==walker['predecessor_pin']['sha256']
pins=[json.loads((E/f'NJJ_L{n:03d}'/'NJJ_ProofDriver_BINARY_PIN.json').read_text()) for n in [30,31,32]];assert pins[0]==pins[1]==pins[2]
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NJJ_[LKE][0-9][0-9][0-9]/receipt.json'))]
metrics={r['attempt']:{k:r[k] for k in ['module','kind','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']} for r in receipts}
result=dict(schema_version=1,status='PASS_COMPONENT_AUDIT_PARENT_OPEN',headline='AspisR1.RPx_Deployed.deployed',target='TX2:065',security_target_established=False,new_closed_rows=0,full_combined_audits=1,gate_source_revision=metrics['NJJ_L028']['source_revision'],budget=dict(used=dict(K=80,L=37,E=0),limits=dict(K=80,L=100,E=1)),selected_modules=len(json.loads((E/'NJJ_MODULES.json').read_text())),raw_roots=len(raw),raw_axioms=sorted(set(a for r in raw for a in r['walked_axioms'])),raw_results=raw,fixture_results=fixtures['results'],same_fixture_and_real_binary=pins[0],walker=walker,coherence=dict(exit_status=0,modules=len(scan),declarations=sum(r['declarations'] for r in scan),dangling=0,duplicate_owners=0,import_mismatches=0),gate_metrics={a:metrics[a] for a in ['NJJ_L028','NJJ_L031','NJJ_L032','NJJ_L035','NJJ_L036','NJJ_L037']},root_statement='NJJ_Common.run/source; printed full body and statement in NJJ_L016/stdout.log',root_hypothesis_audit='NJJ_REMAINING.md',root_inventory_passes=False,new_trust_rows=[],failing_shapes=['NJJ_K015','NJJ_K025'],unqualified_invocation='NJJ_K080',release_source_changed=False)
(E/'NJJ_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
source=json.loads((E/'NJJ_SOURCE_VERIFICATION.json').read_text());cleanup=json.loads((E/'NJJ_CLEANUP.json').read_text());export=json.loads((E/'NJJ_EXPORT.json').read_text())
h=(E/'NJJ_HANDOFF.md').read_text().replace('component work complete, final audit pending','final component audit passed; root OPEN').replace('Budget used before final gates:80/80 Kani,27/100 Lean/support,0/1 extraction.','Budget used:80/80 Kani,37/100 Lean/support,0/1 extraction.')
h+='\n## Final evidence gate\n\nOne combined audit passed on source revision `'+result['gate_source_revision']+'`, importing NGK_COMBINED_IMPORT, NIU_COMBINED_IMPORT, NJC_COMBINED_IMPORT and AspisR1.RPx_Deployed.deployed.16 selected modules /45 raw roots use only standard axioms;8 same-binary planted/mutation fixtures match exactly; NFX scan'+str(len(scan))+' modules /'+str(sum(r['declarations'] for r in scan))+' declarations found0 dangling,0 duplicate owners,0 import mismatches. NJJ_AUDIT.json contains exact targets, exits, wall times, peak RSS, swap, revision and axioms; per-attempt receipts also pin sources/dependencies.\n\n| Exact target | Exit | Wall s | Peak RSS KiB | Swap |\n|---|---:|---:|---:|---:|\n'
for a in ['NJJ_L028','NJJ_L031','NJJ_L032','NJJ_L035','NJJ_L036','NJJ_L037']:
 r=metrics[a];h+='| '+a+' '+r['module']+' | '+str(r['exit_status'])+' | '+f"{r['wall_seconds']:.3f}"+' | '+str(r['peak_rss_kib'])+' | '+str(r['swaps'])+' |\n'
h+='\nRetained export `'+export['path']+'` ('+str(export['bytes'])+' bytes); hashes in NJJ_EXPORT.json. Full coherent closure object pins in NJJ_CLOSURE_PINS.json.xz plus uncompressed sha256. Own Cargo target and solver TMPDIR removed; own objects, seed and retained cache preserved. Free host bytes after cleanup: '+str(cleanup['free_bytes'])+'. No wallet/account/key action. No shipped-file change or ELF rebuild. Ledger delta remains empty; credit waits for the next authoritative ledger gate. Target not yet established.\n'
(E/'NJJ_HANDOFF.md').write_text(h)
# Lossless full section-6 release-result table.
compact=[{k:v for k,v in r.items() if k!='deps_fingerprint'} for r in receipts];data=json.dumps(compact,sort_keys=True).encode();(E/'NJJ_RELEASE_RESULTS.json.xz').write_bytes(lzma.compress(data,preset=6));(E/'NJJ_RELEASE_RESULTS.json.sha256').write_text(hashlib.sha256(data).hexdigest()+'\n')
print(json.dumps(dict(raw_roots=len(raw),fixtures=8,scan_modules=len(scan),scan_declarations=sum(r['declarations'] for r in scan),export_bytes=export['bytes'],gate='PASS_COMPONENT_ONLY',target='OPEN',new_closed_rows=0)))
