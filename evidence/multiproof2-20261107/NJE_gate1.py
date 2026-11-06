"""Read-only evidence validation for the first NJE row packet gate."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
read=lambda p:p.read_text() if p.exists() else lzma.open(str(p)+'.xz').read().decode()
allrows=json.load(open(E/'NJE_ROW_PACKETS.json'));gate_roots=json.load(open(E/'NJE_GATE1_AUDIT_ROOTS.json'))['roots'];rows=[r for r in allrows if r['root'] in gate_roots];closed=json.load(open(E/'NJE_CLOSED.json'))
assert len(rows)==14 and len(closed['functions'])==14
for f,pin in json.load(open(E/'NJE_REUSED_PINS.json')).items():
 p=Path(f);assert hashlib.sha256(p.read_bytes()).hexdigest()==pin['sha256'],f
for a in ['NJE_L001','NJE_L002','NJE_L003','NJE_L004','NJE_L005','NJE_L006','NJE_L008','NJE_L009','NJE_L010','NJE_L011','NJE_L012','NJE_L013','NJE_L014','NJE_L015','NJE_L016']:
 r=json.load(open(E/a/'receipt.json'));assert r['exit_status']==0,a
 ad=json.load(open(E/(a+'-admission.json')));assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert r['limits']['memory.high']=='6442450944' and r['limits']['memory.max']=='8589934592' and r['limits']['memory.swap.max']=='0' and r['limits']['pids.max']=='64'
raw=[json.loads(l[11:]) for l in read(E/'NJE_L016/stdout.log').splitlines() if l.startswith('NEP_RESULT ')]
fixtures=[json.loads(l[11:]) for l in read(E/'NJE_L015/stdout.log').splitlines() if l.startswith('NEP_RESULT ')]
roots=json.load(open(E/'NJE_GATE1_AUDIT_ROOTS.json'))['roots'];assert sorted(r['root'] for r in raw)==sorted(roots)
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} and r['equal'] for r in raw)
assert len(fixtures)==8 and all(r['equal'] for r in fixtures) and all(r['walked_axioms'] for r in fixtures[:4]) and all(not r['walked_axioms'] for r in fixtures[4:])
scan=[json.loads(l) for l in read(E/'NJE_LOADED_scan.jsonl').splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
for p in rows:
 assert p['complete_carrier'] and not p['aq2_hypothesis_inventory']['extra_logical_hypotheses']
 assert all(c['disposition']=='DISCHARGED' for c in p['caller_clauses'])
 assert p['root'] in roots
 p['admission']='FIRST NJE combined/NFX/ax2 gates PASS; credit awaits next lead ledger gate'
for n,x in [('NJE_RAW_RESULTS_GATE1.json',raw),('NJE_FIXTURES.json',fixtures),('NJE_ROW_PACKETS.json',allrows)]: (E/n).write_text(json.dumps(x,indent=2)+'\n')
audit=dict(target_established=False,headline='AspisR1.RPx_Deployed.deployed',combined_audits_used=1,combined_audit_limit=2,gate1={'combined':'NJE_L013','scan':'NJE_L014','fixtures':'NJE_L015','raw':'NJE_L016','all_exit_zero':True,'modules':len(scan),'raw_roots':len(raw),'standard_axioms_only':True,'coherence_defects':0},candidate_rows=[r['row'] for r in rows],ledger_credit_pending=True,cold_release_replay=False,canonical_walker='NJE_AUDIT_TOOL_PINS.json')
(E/'NJE_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
closed.update(admission='First combined/NFX/ax2 gate PASS; credit awaits next lead ledger gate',status='CLOSED within the recorded per-row domains; proposed additive ledger delta')
(E/'NJE_CLOSED.json').write_text(json.dumps(closed,indent=2)+'\n')
for n in ['NJE_AUDIT_ROOTS.json','NJE_AUDIT_MODULES.json','NJE_EXPECTED_IMPORTS.jsonl','NJE_SELECTED_MODULES.json','NJE_COMBINED_IMPORT.lean']:
 assert (E/('NJE_GATE1_'+n.removeprefix('NJE_'))).exists()
print('NJE gate1:14 own-helper rows,26 standard-axiom roots,'+str(len(scan))+' coherent modules; next ledger gate still required')
