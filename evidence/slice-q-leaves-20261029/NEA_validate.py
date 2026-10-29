"""Own evidence integrity checks. Does not override the authoritative NDT adoption gate."""
from pathlib import Path
import json,hashlib,re,subprocess,sys,collections
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;ROOT=E.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(l) for l in (E/'NEA_ATTEMPTS.jsonl').read_text().splitlines() if l.strip()]
assert len({r['attempt'] for r in rows})==len(rows)
counts=collections.Counter(r['attempt'][4] for r in rows)
assert counts=={'K':80,'L':80,'E':20},counts
by={r['attempt']:r for r in rows}
for r in rows:
 a=r['attempt'];actual=json.loads((E/a/'receipt.json').read_text());assert r==actual,a
 for k in ['source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','source_hashes','command','limits']:assert k in r,(a,k)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},(a,r['limits'])
 assert str(r['swaps'])=='0',(a,r['swaps'])
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 if r['kind']=='kani':
  g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen'] and g['exact_frozen_selected_graph'],a
  lock=json.loads((E/(a+'-lock-check.json')).read_text());assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  source=json.loads((E/(a+'-source-check.json')).read_text());assert not source['errors'],a
  assert r['env']['CARGO_NET_OFFLINE']=='true'
  assert r['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert (E/a/'NEA_harness.patch').exists(),a
closed=json.loads((E/'NEA_CLOSED.json').read_text());assert len(closed)==3
axioms=[]
for c in closed:
 assert c['status']=='CLOSED-CONDITIONAL' and c['domain_statement'] and c['physical_interpretation']
 for path in c['lean_receipt_paths']:
  r=json.loads((E/path).read_text());assert r['exit_status']==0,(c['claim_id'],path)
  for line in r['print_axioms']:
   assert not any(s in line for s in ['sorryAx','depends on axioms: [source','depends on axioms: [circle','depends on axioms: [line']),line
 for path in c['kani_receipt_paths']:
  r=json.loads((E/path).read_text());assert r['exit_status']==0,(c['claim_id'],path)
  assert 'VERIFICATION:- SUCCESSFUL' in (E/Path(path).parent/'stdout.log').read_text(),path
 for path in c['control_receipts']:
  r=json.loads((E/path).read_text());log=(E/Path(path).parent/'stdout.log').read_text()
  assert 'timed out' not in log.lower() and 'error: could not compile' not in log,path
  assert ('VERIFICATION:- SUCCESSFUL' if r['exit_status']==0 else 'VERIFICATION:- FAILED') in log,path
for r in rows:
 if r['kind']!='lean':continue
 a=r['attempt']
 for line in r['print_axioms']:
  names=[]
  if 'depends on axioms:' in line:
   names=[s.strip() for s in line.split('depends on axioms: [',1)[1].rstrip(']').split(',')]
  accepted=r['exit_status']==0 and set(names)<= {'propext','Classical.choice','Quot.sound'}
  if r['exit_status']==0:assert accepted,(a,line)
  axioms.append(dict(attempt=a,line=line,accepted=accepted,receipt=a+'/receipt.json'))
(E/'NEA_AXIOMS.json').write_text(json.dumps(axioms,indent=2)+'\n')
# Use the lead validator's actual invariant check on the untouched ledger copy.
sys.path.insert(0,str(ROOT/'evidence/native-ledger3-20261029'))
import NDT_validate
ledger=json.loads((E/'NEA_NDT_LEDGER.json').read_text());NDT_validate.validate_invariants(ledger)
assert sha(E/'NEA_NDT_LEDGER.json')==sha(ROOT/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
assert all(r['composed_status']=='OPEN' for r in ledger['rows'])
assert not subprocess.check_output(['git','diff','--name-only','c2adb7682a^','--','crates','programs'],cwd=ROOT,text=True).strip()
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
from NEA_restore import native
assert (E/'NEA_native.patch').read_bytes()==(E/'NEA_K080/NEA_harness.patch').read_bytes()
if (E/'NEA_PAYLOAD.json').exists():assert native()==json.loads((E/'NEA_PAYLOAD.json').read_text())
delta=json.loads((E/'NEA_LEDGER_DELTA.json').read_text())
assert delta['local_claims']==closed and not delta['composed_row_promotions'] and not delta['canonical_row_mutations']
assert len(delta['functions'])==20 and len({x['function'] for x in delta['functions']})==20
assert all(x['composed_status']=='OPEN' for x in delta['functions'])
assert sum(x['local_status']=='CLOSED-CONDITIONAL' for x in delta['functions'])==3
refs=json.loads((E/'NEA_REFERENCE_RESULTS.json').read_text())
for x in refs:
 for name,h in x['lean_outputs'].items():assert sha(E/name)==h,(x['attempt'],name)
 if x['forbidden_declarations']:assert all(name.endswith('.lean.txt') for name in x['lean_outputs']),x['attempt']
for file in E.rglob('*.lean'):
 assert not re.search(r'^\s*(axiom|sorry|admit)\b|\bnative_decide\b',file.read_text(),re.M),str(file)
result=dict(exit_status=0,checks='Own integrity plus NDT_validate.validate_invariants only; full NDT adoption separately rejects changed report corpus',attempts=len(rows),budget_slots=dict(counts),kani_runs=sum(r['kind']=='kani' for r in rows),inspection_slots=sum(r['kind']=='inspect' for r in rows),conditional_local_claims=len(closed),composed_promotions=0,standard_axiom_lines=sum(x['accepted'] for x in axioms),canonical_ledger_sha256=sha(E/'NEA_NDT_LEDGER.json'),full_ndt_exit_status=1,full_ndt_reason=(E/'NEA_NDT_VALIDATION.stderr').read_text().strip())
(E/'NEA_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
