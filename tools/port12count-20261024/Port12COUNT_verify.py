from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/port12count-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean';T=R/'tools/port12count-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(T/'Port12COUNT_audit_gen.py'),'--check'],check=True)
subprocess.run(['python3',str(T/'Port12COUNT_ledger.py')],check=True)
m=json.loads((E/'manifest.json').read_text());assert m['inherited_lean_attempts']==185
assert m['new_lean_attempts']==28 and m['cumulative_lean_attempts']==213 and m['remaining_lean_attempts']==7
assert m['allocated_lean_slots']==29 and m['pre_lean_rejections']==1
assert m['kani_runs']==0 and m['kani_limit']==20
prior=R/m['prior_ledger']['path']; assert sha(prior)==m['prior_ledger']['sha256']
assert json.loads(prior.read_text())['cumulative_lean_attempts']==185
expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for p in E.glob('lean-*/receipt.json'):
 r=json.loads(p.read_text());assert r['limits']==expected and r['swaps']=='0'
 for src,h in r['source_hashes'].items():assert sha(p.parent/'sources'/src)==h
 assert r['source_revision'] and r['command'] and r['wall_seconds']>0 and int(r['peak_rss_kib'])>0
 assert r['deps_fingerprint']['selected_objects'] and r['deps_fingerprint']['direct_source_hashes']
 for obj in r['deps_fingerprint']['selected_objects'].values():assert len(obj['sha256'])==64 and obj['bytes']>0
 gate=json.loads((E/(r['attempt']+'-reservation.json')).read_text())
 assert gate['reserved_bytes']+gate['additional_bytes']<gate['limit_bytes']==55*1024**3
 if r['exit_status']==0:assert 'sorryAx' not in (p.parent/'stdout.log').read_text()
assert set(m['final_sources'])=={p.name for p in L.glob('Port12COUNT_*.lean')}
for src,v in m['final_sources'].items():assert sha(L/src)==v['sha256']
audit=E/'lean-029';r=json.loads((audit/'receipt.json').read_text());assert r['exit_status']==0
log=(audit/'stdout.log').read_text();decls=json.loads((E/'owned-declarations.json').read_text())
reports=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log))
theorems={d['name'] for d in decls if d['kind']=='theorem'};assert set(reports)==theorems and len(theorems)==36
for axioms in reports.values():assert set(re.findall(r'[A-Za-z][A-Za-z.]*',axioms))<={'propext','Classical.choice','Quot.sound'}
for p in L.glob('Port12COUNT_*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b',p.read_text()),p
 assert not re.search(r'^\s*axiom\b',p.read_text(),re.M),p
changed=subprocess.check_output(['git','diff','--name-only','431346f95327cbda7d7d8ec5c80f881165f162a9'],cwd=R,text=True).splitlines()
for f in changed:
 assert f.startswith(('tools/port12count-20261024/','evidence/port12count-20261024/','docs/research/100bit-spend-path-20261013/lean/Port12COUNT_')),f
 assert not f.endswith(('.olean','.ir','.tar','.gz','.elf')),f
for p in E.rglob('*.json'):assert p.stat().st_size<=5_000_000,p
assessment={'base_revision':'431346f95327cbda7d7d8ec5c80f881165f162a9','scope':'New Port12COUNT proof/tools/evidence only; no shipped source, keys or Session A files changed','reused':'Port9 physical reification/source equations and Port11 leaf/writer plus Port9 reader bounds, selected cached direct objects pinned in each receipt; not a coherent release replay or new ELF identity gate','source_hashes':{p.name:sha(p) for p in sorted(L.glob('Port12COUNT_*.lean'))},'accepted_current_elf_pins':{'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},'new_elf_gate':False}
(E/'source-assessment.json').write_text(json.dumps(assessment,indent=2)+'\n')
result={'status':'pass','final_modules':len(m['final_sources']),'theorem_axiom_reports':len(reports),'actual_lean_attempts':28,'pre_lean_rejections':1,'cumulative_actual_lean':213,'remaining_actual_lean':7,'conservatively_unreserved_slots':6,'audit_receipt':str((audit/'receipt.json').relative_to(R)),'audit_sha256':sha(audit/'receipt.json'),'full_signatures_and_axioms':str((audit/'stdout.log').relative_to(R)),'no_full_manifest_or_new_identity_gate':True}
(E/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
