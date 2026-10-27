from pathlib import Path
import json,hashlib,re,subprocess,ast
E=Path(__file__).resolve().parent
rows=[];errors=[]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for p in sorted(E.glob('NBB_[LKG]*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];kind=r['kind'];log=(p.parent/'stdout.log').read_text()
 if r['limits']!=limits:errors.append([a,'caps'])
 ad=json.loads((E/(a+'-reservation.json')).read_text())
 if ad.get('allowed') is not True:errors.append([a,'admission'])
 for n,h in r['source_hashes'].items():
  q=p.parent/'sources'/n
  if q.is_file() and hashlib.sha256(q.read_bytes()).hexdigest()!=h:errors.append([a,n,'source hash'])
 if kind=='lean' and '-M7000' not in r['command']:errors.append([a,'Lean M cap'])
 if kind=='kani':
  metadata=json.loads((E/a.replace('_K','_G')/'receipt.json').read_text())
  if metadata['source_hashes']!=r['source_hashes']:errors.append([a,'source drift between graph and proof'])
  g=json.loads((E/(a+'-graph-check.json')).read_text())
  if not g['exact_frozen_resolved_graph_match'] or not g['lock_unchanged'] or g['lock_before_sha256']!=g['lock_after_sha256']:errors.append([a,'graph/lock'])
  if r['env']['CARGO_NET_OFFLINE']!='true' or r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']!='3':errors.append([a,'offline/optimized'])
  if '--locked' in r['command']:errors.append([a,'unsupported Kani locked flag'])
 if kind=='lean' and r['exit_status']==0:
  for line in r['print_axioms']:
   m=re.search(r'axioms: \[([^\]]*)\]',line)
   if m and set(m.group(1).split(', '))-{'propext','Classical.choice','Quot.sound'}:errors.append([a,'axioms',line])
 rows.append({k:r[k] for k in ['attempt','kind','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}|{'credited':r['exit_status']==0,'timed_out':'CBMC timed out' in log or r['exit_status']==124})
lean=[r for r in rows if r['kind']=='lean'];kani=[r for r in rows if r['kind']=='kani'];meta=[r for r in rows if r['kind']=='metadata']
audit=json.loads((E/'NBB_L019/receipt.json').read_text());assert audit['exit_status']==0
names=json.loads((E/'NBB_THEOREMS.json').read_text());seen=[re.search("'([^']+)'",x).group(1) for x in audit['print_axioms']]
if sorted(names)!=sorted(seen):errors.append('final audit coverage')
for p in E.glob('NBB_*.lean'):
 s=p.read_text()
 if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)|^import\s+XRn',s,re.M):errors.append([p.name,'forbidden source'])
 if p.name=='NBB_Audit.lean':continue
 accepted=[r for r in lean if r['exit_status']==0 and any(n.endswith('/'+p.name) for n in r['source_hashes'])]
 if not accepted:errors.append([p.name,'no successful source snapshot']);continue
 latest=accepted[-1]
 h=next(h for n,h in latest['source_hashes'].items() if n.endswith('/'+p.name))
 if hashlib.sha256(p.read_bytes()).hexdigest()!=h:errors.append([p.name,'final source differs from accepted snapshot'])
for p in E.glob('NBB_*.py'):ast.parse(p.read_text())
style=[]
for p in [*E.glob('NBB_*.lean'),*E.glob('NBB_*.py'),*E.glob('NBB_*.md')]:
 for i,line in enumerate(p.read_text().splitlines(),1):
  if line.rstrip()!=line:style.append([p.name,i])
if style:errors.append(['authored trailing whitespace',style])
base='1a4fed5579d70e6f2161892ef9d9569814397043'
changed=subprocess.check_output(['git','diff','--name-only',base,'--'],text=True).splitlines()
if any(not n.startswith('evidence/native-query1-20261027/') for n in changed):errors.append(['outside assigned evidence',changed])
tracked=subprocess.check_output(['git','ls-files','evidence/native-query1-20261027'],text=True).splitlines()
if any(Path(n).suffix in ['.pyc','.olean','.o','.a','.so','.elf'] for n in tracked):errors.append('committed binary')
def summary(rs):return dict(attempts=len(rs),passes=sum(r['exit_status']==0 for r in rs),failures=sum(r['exit_status']!=0 for r in rs),wall_seconds=sum(r['wall_seconds'] for r in rs),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swaps=sum(int(r['swaps']) for r in rs))
out=dict(status='OPEN',headline_premises_removed=0,lean=summary(lean),kani=summary(kani),metadata=summary(meta),budgets=dict(lean_max=100,kani_max=30,exhausted=False),final_audit='NBB_L019',new_theorems=len(names),final_audit_metrics={k:audit[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']},errors=errors,authored_style_errors=style,attempts=rows)
(E/'NBB_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'NBB_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
assert not errors,errors
print(json.dumps({k:out[k] for k in ['status','lean','kani','metadata','new_theorems','errors']}))
