"""Additive S2 parser checks; inherited ledger predicates are never relaxed.
Read-only except for the NGV validation receipt. No prover runs here.
"""
from pathlib import Path
import json,lzma,hashlib,copy,re,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
standard={'propext','Classical.choice','Quot.sound'}
if (E/'NGV_PACK.json').exists():
 for entry in J(E/'NGV_PACK.json')['entries']:
  data=lzma.decompress((E/entry['blob']).read_bytes())
  assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256']
  assert J(E/(entry['original']+'.REFERENCE.json'))==entry
base=R/'evidence/inv-repair-20261104/NGB_ADMITTED_LEDGER.json.xz'
rows={r['row']:r for r in json.loads(lzma.decompress(base.read_bytes()))['rows']};assert len(rows)==599
for p in J(E/'NGV_REUSED.json'):assert sha(R/p['path'])==p['sha256']
for p in J(R/'evidence/slice-d-parser2-20261105/NGO_REUSED.json'):assert sha(R/p['path'])==p['sha256'] and p['replayed'] is False
assert sha(R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
closed=J(E/'NGV_CLOSED.json');delta=J(E/'NGV_LEDGER_DELTA.json');edges=J(E/'NGV_EDGES.json')
audit=J(E/'NGV_AUDIT.json');summary=J(E/audit['summary']);assert summary['status']=='PASS'
raw={r['root']:r for c in summary['commands']if c['target'].startswith('proof')for r in c['results']}
assert 'AspisR1.RPx_Deployed.deployed' in raw
for r in raw.values():assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<=standard
fixtures=next(c for c in summary['commands']if c['target']=='fixtures')['results'];assert len(fixtures)==8
assert all(len(r['walked_axioms'])==1 for r in fixtures[:4]) and all(not r['walked_axioms']for r in fixtures[4:])
scan=[json.loads(l)for l in (E/audit['scan']).read_text().splitlines()]
assert len(scan)>12000 and all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
assert J(E/'NGV_WALKER_IDENTITY.json')['equal']
assert 'import NGK_COMBINED_IMPORT' in (E/'NGV_COMBINED_IMPORT.lean').read_text()
for a in audit['attempts']:
 r=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'))
 assert r['exit_status']==0 and ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(r['swaps'])==0
successes=[J(p) for p in E.glob('NGV_L*/receipt.json') if J(p)['kind']=='lean' and J(p)['exit_status']==0]
for f in closed['functions']:
 for p in f['sources']:
  assert sha(E/p['path'])==p['sha256']
  key='NGV_generated/'+p['path']
  assert any(r['source_hashes'].get(key)==p['sha256'] for r in successes),p['path']
 for pair in f['native_pairs']:
  for n,verdict in zip(pair,['SUCCESSFUL','FAILED']):
   p=R/'evidence/slice-d-parser-20261104'/n
   assert 'VERIFICATION:- '+verdict in (p/'stdout.log').read_text()
   receipt=J(p/'receipt.json');assert receipt['exit_status']==(0 if verdict=='SUCCESSFUL'else 1)
   assert receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
allowed={'TX1:151':('NGV_ParsePacket.result','NGV_ParsePacket'), 'TX1:152':('NGV_AtPacket.result','NGV_AtPacket'), 'TX1:098':('NGV_SemanticPacket.result','NGV_SemanticPacket')}
def validate(c,d,es):
 assert c['driver_root_status']=='OPEN' and c['new_composed_functions']==len(c['functions'])==c['new_composed_rows']
 selected=[r for f in c['functions']for r in f['rows']]
 assert len(selected)==len(set(selected)) and set(selected)<=set(allowed)
 assert d['checks_added_only'] and d['baseline_sha256']==sha(base) and d['new_closed_rows']==selected and d['no_other_status_change']
 assert len(d['rows'])==len(selected)
 for f in c['functions']:
  assert len(f['rows'])==1;r=f['rows'][0];old=rows[r]
  assert f['function']==old['function'] and f['frozen_body_sha256']==old['frozen_body_sha256']
  assert f['status']=='CLOSED' and not f['inner_hypotheses_remaining'] and f['retained_root_interpretation']
  root,module=allowed[r];assert f['lean_root']==root and f['canonical_module']==module and root in raw
  required={'TX1:151':[[45,46],[47,48],[49,50]],'TX1:152':[[55,56],[57,58]],
   'TX1:098':[[59,60],[61,62]]+[[n,n+1]for n in range(64,92,2)]+[[92,93],[94,95]]}[r]
  assert f['native_pairs']==[[f'NGD_K{n:03d}'for n in pair]for pair in required]
  actual=[e for e in es if e['row']==r]
  assert set(e['callee']for e in actual)==set(old['canonical_callees'])
  assert all(e['status']=='CLOSED'and e['proof']and e['citation']for e in actual)
  assert set(f['domain_roots'])<=set(raw)
  assert all(x['before']=='OPEN'and x['after']=='CLOSED'for x in d['rows'])
validate(closed,delta,edges)
controls=[]
for name,change in [
 ('open inner callee',lambda c,d,e:c['functions'][0].update(inner_hypotheses_remaining=['missing'])),
 ('wrong root',lambda c,d,e:c['functions'][0].update(lean_root='True.intro')),
 ('wrong owner',lambda c,d,e:c['functions'][0].update(canonical_module='NGO_DecodePort')),
 ('missing control',lambda c,d,e:c['functions'][0].update(native_pairs=[])),
 ('wrong body',lambda c,d,e:c['functions'][0].update(frozen_body_sha256='0'*64)),
 ('single missing native pair',lambda c,d,e:c['functions'][0]['native_pairs'].pop()),
 ('open edge',lambda c,d,e:next(x for x in e if x['row']==c['functions'][0]['rows'][0]).update(status='OPEN')),
 ('extra closure',lambda c,d,e:d['new_closed_rows'].append('TX1:147')),
 ('changed baseline',lambda c,d,e:d.update(baseline_sha256='0'*64))]:
 c,d,e=copy.deepcopy((closed,delta,edges));change(c,d,e)
 try:validate(c,d,e)
 except AssertionError:controls.append(name)
 else:raise AssertionError('accepted corruption: '+name)
result=dict(status='PASS',checks_added_only=True,new_closed_rows=delta['new_closed_rows'],raw_roots=len(raw),scan_modules=len(scan),mutations_rejected=controls)
(E/'NGV_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
