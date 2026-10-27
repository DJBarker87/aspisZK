"""Audit receipts, exact source patches, budget, graphs and accepted axioms."""
from pathlib import Path
import json,hashlib,subprocess,tempfile,re
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
errors=[];allr=[];ks=[];ls=[];accepted={}
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
frozen_lock=hashlib.sha256(subprocess.check_output(['git','show',F+':Cargo.lock'])).hexdigest()
for p in sorted(E.glob('LPf_*/receipt.json')):
 r=json.loads(p.read_text());allr.append(r);a=r['attempt'];kind=r['kind']
 for key in ['command','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','source_hashes','print_axioms','deps_fingerprint']:
  if key not in r:errors.append([a,'missing',key])
 if r['limits']!=limits:errors.append([a,'limits'])
 if int(r['swaps'])!=0:errors.append([a,'swap'])
 ad=json.loads((E/(a+'-reservation.json')).read_text())
 if ad.get('allowed') is not True:errors.append([a,'unadmitted'])
 if not re.fullmatch('[0-9a-f]{40}',r['source_revision']):errors.append([a,'revision'])
 if kind=='kani':
  ks.append(r);g=json.loads((E/(a+'-graph-check.json')).read_text())
  m=json.loads((E/a.replace('_K','_G')/'stdout.log').read_text())
  keys={v['id']:json.dumps([v['name'],v['version'],v.get('source')],separators=(',',':')) for v in m['packages']}
  graph={'packages':sorted(keys.values()),'edges':sorted([keys[n['id']],sorted(keys[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
  if graph!=json.loads((E/'LPf_frozen_graph.json').read_text()):errors.append([a,'exact frozen graph mismatch'])
  if not (g['package_and_edges_match'] and g['lock_unchanged'] and g['lock_before_sha256']==frozen_lock==g['lock_after_sha256']):errors.append([a,'graph/lock'])
  if r['env'].get('CARGO_NET_OFFLINE')!='true' or r['env'].get('CARGO_PROFILE_DEV_OPT_LEVEL')!='3':errors.append([a,'profile/offline'])
  if '--locked' in r['command']:errors.append([a,'unsupported kani flag'])
  patch=p.parent/'LPf_harness.patch'
  if not patch.exists():errors.append([a,'missing patch']);continue
  with tempfile.TemporaryDirectory(prefix='LPf_audit_') as td:
   root=Path(td).resolve()
   for f in r['source_hashes']:
    rel=f.removeprefix('LPf_src/');old=subprocess.run(['git','show',F+':'+rel],capture_output=True)
    if old.returncode==0:
     dest=root/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(old.stdout)
   ap=subprocess.run(['git','apply','--unidiff-zero','--unsafe-paths','--directory',str(root),str(patch)],capture_output=True,text=True)
   if ap.returncode:errors.append([a,'patch apply',ap.stderr]);continue
   for f,sha in r['source_hashes'].items():
    q=root/f.removeprefix('LPf_src/')
    if not q.exists() or hashlib.sha256(q.read_bytes()).hexdigest()!=sha:errors.append([a,'source hash',f])
 if kind=='lean':
  ls.append(r)
  if r['exit_status']==0:
   if not r['print_axioms']:errors.append([a,'missing successful audit'])
   for line in r['print_axioms']:
    if 'depends on axioms:' in line:
     names=line.split('[')[1].split(']')[0].split(', ')
     if set(names)-{'propext','Classical.choice','Quot.sound'}:errors.append([a,'unaccepted axioms',line])
   for f,sha in r['source_hashes'].items():
    snapshot=p.parent/'sources'/f
    if not snapshot.exists() or hashlib.sha256(snapshot.read_bytes()).hexdigest()!=sha:errors.append([a,'Lean snapshot',f])
    accepted[Path(f).name]=(a,sha)
for p in Path('lean').glob('LPf_*.lean'):
 if p.name not in accepted or accepted[p.name][1]!=hashlib.sha256(p.read_bytes()).hexdigest():errors.append(['unchecked current module',str(p)])
 if re.search(r'\b(sorry|admit|native_decide)\b|^axiom |^set_option max(?:RecDepth|Heartbeats)',p.read_text(),re.M):errors.append(['forbidden proof',str(p)])
if len(ks)>30 or len(ls)>60:errors.append(['budget',len(ks),len(ls)])
for m in ['FJv_Top','ARX_Root']:
 before=(E/('LPf_'+m+'.BEFORE.lean.txt')).read_bytes();after=Path('lean',m+'.lean').read_bytes()
 if before!=after:errors.append(['top changed',m])
 (E/('LPf_'+m+'.AFTER.lean.txt')).write_bytes(after)
def stats(rs):return {'attempts':len(rs),'passed':sum(r['exit_status']==0 for r in rs),'wall_seconds':sum(r['wall_seconds'] for r in rs),'peak_rss_kib':max([int(r['peak_rss_kib']) for r in rs],default=0),'swaps':sum(int(r['swaps']) for r in rs)}
out={'metadata_counts_are_process_exit_status_only':True,'required_infrastructure_stop':'G033 JSONDecodeError before graph-pass/Kani launch; no subsequent proof run','kani':stats(ks),'lean':stats(ls),'metadata':stats([r for r in allr if r['kind']=='metadata']),'accepted_modules':{k:{'attempt':v[0],'sha256':v[1]} for k,v in accepted.items()},'errors':errors}
(E/'LPf_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['accepted_modules','errors']},indent=2));print('audit errors:',len(errors))
if errors:raise SystemExit('source/receipt audit failed: '+str(len(errors)))
