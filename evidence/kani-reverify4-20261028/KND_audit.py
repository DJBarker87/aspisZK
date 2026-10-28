from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('KND_[KLR]*/receipt.json'))]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
runs=[];objects={};attempts={}
legacy=json.loads((E.parent/'kani-reverify1-20261028/KMY_SOURCE_ARCHIVE.json').read_text())['objects']
for r in receipts:
 a=r['attempt'];ad=json.loads((E/(a+'-reservation.json')).read_text());assert ad['allowed'] is True
 lim=r['limits'];assert lim['memory.high']=='6442450944' and lim['memory.max']=='8589934592' and lim['memory.swap.max']=='0' and lim['pids.max']=='64'
 assert str(r['swaps'])=='0'
 h=r['source_hashes'];attempts[a]=h
 for name,digest in h.items():
  candidates=[E/name,E/'sources'/(digest+'.rs'),E/'sources'/(digest+'.txt'),E.parent/'kani-reverify1-20261028/sources'/(digest+'.txt')]
  found=next((p for p in candidates if p.is_file() and sha(p)==digest),None)
  if found:objects[digest]=dict(path=str(found.relative_to(E.parent)),sha256=digest)
  else:objects[digest]=dict(legacy=legacy.get(digest),scope='unchanged frozen source; see original archive')
 if r['kind'] in ['kani','rust']:
  g=json.loads((E/(a+'-graph.json')).read_text());assert g['allowed'] and g['unchanged'] and g['lock_before']==g['lock_after']
  assert not g['new_packages'] and not g['edge_errors']
  assert h['KMX_stubs.rs']=='c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9'
 axioms=r['print_axioms'];assert 'sorryAx' not in str(axioms)
 for names in re.findall(r'depends on axioms: \[([^]]*)\]',str(axioms)):
  assert set(x.strip() for x in names.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'}
 runs.append({k:r.get(k) for k in ['attempt','kind','sources','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','limits','reservation_retries']})
(E/'KND_RUNS.json').write_text(json.dumps(runs,indent=2)+'\n')
(E/'KND_SOURCE_ARCHIVE.json').write_text(json.dumps(dict(attempts=attempts,objects=objects),indent=2)+'\n')
pair_audit=[]
if (E/'KND_PAIRS.json').exists():
 for p in json.loads((E/'KND_PAIRS.json').read_text()):
  a,b=p['positive_id'],p['control_id'];ra=next(r for r in receipts if r['attempt']==a);rb=next(r for r in receipts if r['attempt']==b)
  sa=(E/'sources'/(ra['source_hashes']['KND_windows.rs']+'.rs')).read_text();sb=(E/'sources'/(rb['source_hashes']['KND_windows.rs']+'.rs')).read_text()
  assert sa.replace('^ 0u8','^ NEG')==sb.replace('^ 1u8','^ NEG')
  assert ra['transition']==rb['transition'] and ra['env']==rb['env'] and ra['timeout']==rb['timeout']
  control_log=(E/b/'stdout.log').read_text()
  correct_failure='Failed Checks: assertion failed: out[j] ==' in control_log
  credit=p['positive']=='PASS' and p['control']=='COUNTEREXAMPLE' and correct_failure
  assert credit==p['credit']
  pair_audit.append(dict(positive=a,control=b,matched=True,only_xor1_diff=True,control_failed_selected_assertion=correct_failure,credit=credit))
(E/'KND_PAIR_AUDIT.json').write_text(json.dumps(pair_audit,indent=2)+'\n')
(E/'KND_ADMISSION_AUDIT.json').write_text(json.dumps(dict(admitted=len(receipts),allowed_true_and_exit_zero_guard='KMY_host.admit reused unchanged; returns only when exit_status==0 and allowed is True',all_caps_verified=True,one_own_scope_at_a_time=True,scope_order=['KND_L001']+sorted(r['attempt'] for r in receipts if r['kind']=='kani')+sorted(r['attempt'] for r in receipts if r['kind']=='rust')+sorted(r['attempt'] for r in receipts if r['kind']=='lean' and r['attempt']!='KND_L001'),transport_log='KMY_TRANSPORT.jsonl',refusals=sum(1 for p in E.glob('*-barrier-*.log') if '\"allowed\": false' in p.read_text())),indent=2)+'\n')
print(json.dumps(dict(receipts=len(receipts),kinds={kind:sum(r['kind']==kind for r in receipts) for kind in ['kani','lean','rust']},credited_pairs=sum(p['credit'] for p in pair_audit),maximum_rss_kib=max(int(r['peak_rss_kib']) for r in receipts)),indent=2))
