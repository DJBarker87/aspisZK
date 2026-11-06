"""Validate the final combined import, strict loaded scan and complete axiom walk."""
from pathlib import Path
import json,lzma,hashlib,sys
sys.dont_write_bytecode=True
import NKB_resolve
E=Path(__file__).resolve().parent;metrics=[]
for n in [100,101,102]:
 a=f'NKB_L{n:03d}';r=json.loads((E/a/'receipt.json').read_text());ad=json.loads((E/(a+'-admission.json')).read_text())
 assert r['exit_status']==0 and ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and str(r['swaps'])=='0'
 metrics.append({k:r[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']})
roots=json.loads((E/'NKB_AUDIT_ROOTS.json').read_text())['roots'];raw=[json.loads(l[11:]) for l in NKB_resolve.read('NKB_L102/stdout.log').decode().splitlines() if l.startswith('NEP_RESULT ')]
assert sorted(x['root'] for x in raw)==sorted(roots)
assert all(x['equal'] and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in raw)
scantext=NKB_resolve.read('NKB_LOADED_scan.jsonl');scan=[json.loads(l) for l in scantext.decode().splitlines()]
assert scan and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in scan)
fixtures=NKB_resolve.read('NKB_AUDIT2_FIXTURES.log').decode()
expected_fixtures={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
fixture_rows=[json.loads(l[11:]) for l in fixtures.splitlines() if l.startswith('NEP_RESULT ')]
assert {x['root'] for x in fixture_rows}==set(expected_fixtures)
assert all(x['equal'] and x['walked_axioms']==x['collect_axioms']==expected_fixtures[x['root']] for x in fixture_rows)
(E/'NKB_FIXTURE_RESULTS.json').write_text(json.dumps(fixture_rows,indent=2)+'\n')
f=json.loads((E/'NKB_L044/receipt.json').read_text());assert f['exit_status']==0
hist=[json.loads(x) for x in (E/'NKB_ATTEMPTS.jsonl').read_text().splitlines()];imports=[x for x in hist if x['kind']=='lean' and x['module']=='NKB_COMBINED_IMPORT'];assert len(imports)==3
result=dict(status='PASS',combined_import_attempts=3,full_combined_audits_completed=2,full_combined_audit_limit=2,prior_complete_audit=json.loads(NKB_resolve.read('NKB_AUDIT1_AUDIT.json')),first_import=dict(attempt='NKB_L045',exit=1,reason='Own LEAN_PATH omitted NJI_COMBINED_IMPORT; corrected from NJW paths and preflighted'),final_metrics=metrics,loaded_modules=len(scan),declarations=sum(x['declarations'] for x in scan),references=sum(x['edges'] for x in scan),cached_replicas=sum(len(x.get('cached_replicas',[])) for x in scan),coherence_defects=0,scan_sha256=hashlib.sha256(scantext).hexdigest(),roots=len(raw),standard_axioms_only=True,raw_equals_collectAxioms=True,fixtures='NKB_L101: fresh eight fidelity controls and recorded binary SHA, checked unchanged again before raw ax2',headline='AspisR1.RPx_Deployed.deployed',closed_rows=0,target_established=False)
(E/'NKB_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');(E/'NKB_RAW_RESULTS.json').write_text(json.dumps(raw,indent=2)+'\n')
(E/'NKB_GATE_LOADED_scan.jsonl.xz').write_bytes(lzma.compress(scantext,preset=6));(E/'NKB_GATE_LOADED_scan.jsonl.sha256').write_text(hashlib.sha256(scantext).hexdigest()+'\n')
(E/'NKB_ROOT_STATEMENTS.md').write_text('# NKB printed statements\n\nTarget not yet established. All are LOCAL SUPPORT / FINDINGS, not positive parent row roots.\n\n```lean\n'+NKB_resolve.read('NKB_L100/stdout.log').decode()+'\n```\n')
print('NKB second/final gate PASS: '+str(len(scan))+' modules, '+str(len(raw))+' raw-standard roots, zero coherence defects; zero admitted rows')
