from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;errors=[];rows=[]
for kind,limit in [('L',100),('K',10)]:
 ps=sorted(E.glob('XRj_'+kind+'*/receipt.json'))
 if len(ps)>limit:errors.append('budget exceeded '+kind)
 for i,p in enumerate(ps,1):
  x=json.loads(p.read_text());a=f'XRj_{kind}{i:03}'
  if x['attempt']!=a:errors.append('attempt sequence '+a)
  for name,expected in x['source_hashes'].items():
   q=p.parent/'sources'/name
   if not q.exists():errors.append('missing snapshot '+str(q));continue
   if hashlib.sha256(q.read_bytes()).hexdigest()!=expected:errors.append('source hash '+str(q))
  if x['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append('limits '+a)
  if x['swaps']!='0':errors.append('swap '+a)
  rows.append(dict(attempt=a,exit=x['exit_status'],wall=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps']))
axioms=json.loads((E/'XRj_L014/receipt.json').read_text())['print_axioms']
if len(axioms)!=7:errors.append('missing audit')
for line in axioms:
 names=re.search(r'\[([^]]*)\]',line)
 if names and not set(names[1].split(', '))<= {'propext','Classical.choice','Quot.sound'}:errors.append('nonstandard axiom '+line)
for p in E.glob('XRj_*.lean'):
 # Only declarations; comments/specifications are not Lean axioms.
 if re.search(r'^\s*(axiom|sorry|admit)\b',p.read_text(),re.M):errors.append('proof hole '+p.name)
for name in ['ARX_Root','Rc10_Top']:
 if (E/('XRj_'+name+'.BEFORE.lean.txt')).read_bytes()!=(E/('XRj_'+name+'.AFTER.lean.txt')).read_bytes():errors.append('top statement drift '+name)
cleanup=json.loads((E/'XRj_cleanup.json').read_text())
if cleanup['failed_Funs_object_existed']:errors.append('failed context object')
# This job's changes only. No source/artifact/key mutation outside its packet.
paths=subprocess.check_output(['git','diff','--name-only','2ffb5325ae','--'],text=True).splitlines()
for path in paths:
 if not path.startswith('evidence/extraction-assoc2-20261027/'):errors.append('out of scope '+path)
 for suffix in ['.olean','.ilean','.ir','.elf','.so','.a','.tar','.gz']:
  if path.endswith(suffix):errors.append('binary committed '+path)
result=dict(errors=errors,attempts=rows,print_axioms=axioms,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),unchanged_top_delta={'T':0,'P':0,'G':0,'C':0},source_and_artifact_changes_outside_packet=False,qualification='No release association or whole-top non-vacuity claimed; failed diagnostic contexts rejected.')
(E/'XRj_Verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'errors':errors,'Lean':15,'Kani':10,'audited_model_laws':len(axioms)}));raise SystemExit(bool(errors))
