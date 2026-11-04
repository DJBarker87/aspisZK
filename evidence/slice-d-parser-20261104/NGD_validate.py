"""Additive NGD checks. Historical evidence/statuses are retained verbatim."""
from pathlib import Path
import json,lzma,hashlib,subprocess,sys,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();J=lambda p:json.loads(p.read_text())
subprocess.run([sys.executable,str(E/'NGD_slot_validate.py')],check=True)
basepath=R/'evidence/inv-repair-20261104/NGB_ADMITTED_LEDGER.json.xz';base=json.loads(lzma.decompress(basepath.read_bytes()));by={r['row']:r for r in base['rows']};assert len(by)==599
roots=J(E/'NGD_ROOTS.json');summary=J(E/'NGD_final_audit/SUMMARY.json');assert summary['status']=='PASS'
audit={r['root']:r for c in summary['commands']if c['target'].startswith('proof')for r in c['results']}
assert set(audit)==set(roots)
for r in audit.values():assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}
scan=[json.loads(l)for l in (E/'NGD_LOADED_scan.jsonl').read_text().splitlines()]
assert len(scan)>12000 and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match']for r in scan)
assert J(E/'NGD_WALKER_IDENTITY.json')['equal']
for a in ['NGD_L013','NGD_L014','NGD_L015','NGD_L016','NGD_L017','NGD_L018','NGD_L019','NGD_L020','NGD_L021']:
 r=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));assert r['exit_status']==0 and ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and int(r['swaps'])==0
closed=J(E/'NGD_CLOSED.json');delta=J(E/'NGD_LEDGER_DELTA.json')
def validate(c,d):
 assert c['new_composed_rows']==2 and len(c['functions'])==1
 packet=c['functions'][0];assert packet['rows']==['TX1:100','TX2:066'] and not packet['inner_hypotheses_remaining']
 assert packet['native_positive']=='NGD_K007'and packet['matched_control']=='NGD_K008'
 assert packet['lean_root']=='NGD_SlotModel.reference' and packet['lean_root']in audit
 assert d['baseline_sha256']==sha(basepath) and d['new_closed_rows']==packet['rows']and d['no_other_status_change']
 for row in packet['rows']:
  assert by[row]['function']==packet['function'] and not by[row]['canonical_callees']and not by[row]['caller_domain_obligations']
 assert len(d['rows'])==2 and all(r['before']=='OPEN'and r['after']=='CLOSED'for r in d['rows'])
validate(closed,delta)
controls=[]
for key,value in [('inner_hypotheses_remaining',['open child']),('matched_control','NGD_K007'),('rows',['TX1:151']),('lean_root','True.intro')]:
 c=copy.deepcopy(closed);c['functions'][0][key]=value
 try:validate(c,delta)
 except AssertionError:controls.append(key)
 else:raise AssertionError('mutation accepted: '+key)
(E/'NGD_VALIDATION.json').write_text(json.dumps(dict(status='PASS',checks_added_only=True,baseline_sha256=sha(basepath),baseline_rows=599,closed_rows=closed['functions'][0]['rows'],scanned_modules=len(scan),raw_roots=len(audit),mutations_rejected=controls,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),claim='Focused hybrid composed packet, not cold release replay or headline premise retirement'),indent=2)+'\n')
