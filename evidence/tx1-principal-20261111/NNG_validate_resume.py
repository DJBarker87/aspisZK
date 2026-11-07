"""Read-only validation of this continuation's own receipts and focused audits."""
from pathlib import Path
import json,hashlib,lzma,subprocess
E=Path(__file__).resolve().parent
standard={'propext','Classical.choice','Quot.sound'}
receipts=[];snapshot_count=0
for f in sorted(E.glob('NNG_L[0-9][0-9][0-9]/receipt.json')):
 if int(f.parent.name[-3:])<476:continue
 d=json.loads(f.read_text());a=d['attempt'];receipts.append(d)
 assert all(k in d for k in ['source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','source_hashes']),a
 assert str(d['swaps'])=='0',a
 assert d['exit_status'] not in [124,137,143],a
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 admission=json.loads((E/(a+'-admission.json')).read_text())
 assert admission['exit']==0 and admission['reservation']['allowed'] is True,a
 for name,expected in d['source_hashes'].items():
  q=f.parent/'sources'/name
  if q.exists():data=q.read_bytes()
  else:data=lzma.decompress(q.with_suffix(q.suffix+'.xz').read_bytes())
  assert hashlib.sha256(data).hexdigest()==expected,(a,name)
  snapshot_count+=1
for label in ['C137','C087','S094']:
 d=json.loads((E/('NNG_'+label+'_AUDIT_SUMMARY.json')).read_text())
 assert d['status']=='PASS' and d['raw_matches_collector'] and d['standard_axioms_only']
 assert all(r['equal'] and set(r['collect_axioms'])<=standard and set(r['walked_axioms'])<=standard for r in d['results'])
latest=json.loads((E/'NNG_S094_AUDIT_ROOTS.json').read_text())['selected_receipts']
for mod,receipt in latest.items():
 f=E/receipt;d=json.loads(f.read_text());rel='NNG_generated/'+mod.replace('.','/')+'.lean'
 assert d['exit_status']==0
 assert (E/rel).read_bytes()==(f.parent/'sources'/rel).read_bytes(),mod
 assert not any('sorryAx' in line for line in d['print_axioms']),mod
all_ids=set()
for f in E.glob('NNG_ATTEMPTS*.jsonl'):
 for line in f.open():
  d=json.loads(line)
  if d.get('kind')!='wait':all_ids.add(d['attempt'])
submitted={d['attempt'] for line in (E/'NNG_TRANSPORT.jsonl').read_text().splitlines() if (d:=json.loads(line)).get('submitted')}
assert not submitted-all_ids,submitted-all_ids
used={g:0 for g in ['lean_link_audit','extract','kani']}
for a in all_ids:
 d=json.loads((E/(a+'.json')).read_text());k=d['kind']
 g='lean_link_audit' if k in ['lean','link','audit'] else k
 if g in used:used[g]+=1
assert used['lean_link_audit']<=550 and used['extract']<=2 and used['kani']<=10
assert not [str(f)for f in E.rglob('*')if f.is_file()and f.stat().st_size>20_000_000]
frozen=subprocess.check_output(['git','rev-parse','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/candidate.rs'],text=True).strip()
actual=subprocess.check_output(['git','hash-object','crates/aspis-r1-cost-probe/src/candidate.rs'],text=True).strip();assert frozen==actual
out=dict(status='PASS',scope_usage=used,prior_scopes=359,continuation_scopes=used['lean_link_audit']-359,client_scope_limit=550,remaining_scopes=550-used['lean_link_audit'],continuation_receipts=len(receipts),snapshots_checked=snapshot_count,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,latest_checked_modules=len(latest),unresolved_submissions=[],no_timeout_or_memory_kill=True,standard_axioms_only=True,shipped_candidate_blob=frozen,scope_summary=[{k:d[k]for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']}for d in receipts])
(E/'NNG_RESUME_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='scope_summary'}))
