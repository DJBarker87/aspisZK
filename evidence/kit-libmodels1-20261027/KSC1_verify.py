from pathlib import Path
import json,hashlib,re,collections
E=Path(__file__).resolve().parent;errors=[];attempts=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for p in sorted(E.glob('KSC1_[LR]*/receipt.json')):
 x=json.loads(p.read_text());attempts.append(x)
 for rel,h in x['source_hashes'].items():
  q=p.parent/'sources'/rel
  if not q.exists() or sha(q)!=h:errors.append('snapshot '+str(q))
 ad=json.loads((E/(x['attempt']+'-admission.json')).read_text())
 if ad['exit_status']!=0 or not ad['allowed']:errors.append('admission '+x['attempt'])
 if x['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append('limits '+x['attempt'])
 if x['exit_status']==0 and x['kind']=='lean':
  if any('sorryAx' in p or any(n not in ['propext','Classical.choice','Quot.sound'] for n in re.findall(r'axioms: \[([^]]*)\]',p)[0].split(', ')) for p in x['print_axioms'] if 'axioms: [' in p):errors.append('axioms '+x['attempt'])
for p in E.glob('KSC1_*.lean'):
 matches=[x for x in attempts if x['kind']=='lean' and x['exit_status']==0 and x['source_hashes'].get('KSC1_generated/'+p.name)==sha(p)]
 if not matches:errors.append('no current exit0 '+p.name)
 if re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text()):errors.append('forbidden '+p.name)
final=next(x for x in attempts if x['attempt']=='KSC1_L015');names=set()
for p in E.glob('KSC1_*.lean'):
 for m in re.finditer(r'^theorem (\S+)',p.read_text(),re.M):names.add((p.stem,m[1]))
assert len(names)==len(final['print_axioms'])==23
rows=json.loads((E/'KSC1_verdicts.json').read_text())['rows'];assert len(rows)==95 and len({r['alphabetical_row'] for r in rows})==95
term=json.loads((E/'KSC1_terminal_state.json').read_text());assert not term['aeneas_mismatches'];assert all(not x['still_present'] for x in term['scopes']);assert term['persistent_cache_present']
lock=json.loads((E/'KSC1_lock.json').read_text());assert lock['unchanged']
lean=[x for x in attempts if x['kind']=='lean'];rust=[x for x in attempts if x['kind']=='rust']
out=dict(errors=errors,lean_attempts=len(lean),lean_pass=sum(x['exit_status']==0 for x in lean),rust_attempts=len(rust),rust_pass=sum(x['exit_status']==0 for x in rust),kani_runs=0,new_theorems=len(names),axioms=final['print_axioms'],lean_total_wall=sum(x['wall_seconds'] for x in lean),lean_peak_rss_kib=max(int(x['peak_rss_kib']) for x in lean),total_swaps=sum(int(x['swaps']) for x in attempts),verdicts=dict(collections.Counter(x['verdict'] for x in rows)),final_target={k:final[k] for k in ['attempt','module','command','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps']})
(E/'KSC1_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
with (E/'KSC1_attempts.jsonl').open('w') as f:
 for x in attempts:f.write(json.dumps(x)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['axioms','final_target']},indent=2))
if errors:raise SystemExit(1)
