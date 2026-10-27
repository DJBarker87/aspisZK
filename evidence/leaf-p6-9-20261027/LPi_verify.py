"""Read-only receipt, exact patch, source and trust-boundary audit."""
from pathlib import Path
import json,hashlib,subprocess,tempfile,re
E=Path(__file__).resolve().parent;R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
errors=[];lean=[];kani=[];latest={}
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for p in sorted(E.glob('LPi_*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt']
 for k in ['command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']:
  if k not in r:errors.append([a,'missing',k])
 if r['limits']!=limits or int(r['swaps'])!=0:errors.append([a,'resources'])
 if json.loads((E/(a+'-reservation.json')).read_text()).get('allowed') is not True:errors.append([a,'admission'])
 if r['kind']=='lean':
  lean.append(r)
  for f,h in r['source_hashes'].items():
   q=p.parent/'sources'/f
   if not q.is_file() or hashlib.sha256(q.read_bytes()).hexdigest()!=h:errors.append([a,'snapshot',f])
  if r['exit_status']==0:
   if not r['print_axioms']:errors.append([a,'missing audit'])
   for line in r['print_axioms']:
    if 'depends on axioms:' in line and not set(line.split('[')[1].split(']')[0].split(', '))<={'propext','Classical.choice','Quot.sound'}:errors.append([a,'axioms',line])
   latest[r['module']]=r
 if r['kind']=='kani':
  kani.append(r)
  if r['env'].get('CARGO_NET_OFFLINE')!='true' or r['env'].get('CARGO_PROFILE_DEV_OPT_LEVEL')!='3':errors.append([a,'offline/profile'])
  if '--locked' in r['command']:errors.append([a,'unsupported cargo-kani flag'])
  g=json.loads((E/(a+'-graph-check.json')).read_text())
  if not(g['exact_frozen_resolved_graph_match'] and g['package_and_edges_match'] and g['lock_unchanged']):errors.append([a,'graph/lock'])
  raw=(E/a.replace('_K','_G')/'stdout.log').read_text();m=json.loads(raw[raw.index('{'):]);keys={v['id']:json.dumps([v['name'],v['version'],v.get('source')],separators=(',',':')) for v in m['packages']}
  graph={'packages':sorted(keys.values()),'edges':sorted([keys[n['id']],sorted(keys[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
  if graph!=json.loads((E/'LPi_frozen_graph.json').read_text()):errors.append([a,'exact graph'])
  with tempfile.TemporaryDirectory(prefix='LPi_patch_audit_') as td:
   root=Path(td).resolve()
   for f in r['source_hashes']:
    rel=f.removeprefix('LPi_src/');assert rel.startswith(('crates/','programs/')) or rel in ['Cargo.lock','Cargo.toml']
    old=subprocess.run(['git','show',R+':'+rel],capture_output=True)
    if old.returncode==0:
     dst=root/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(old.stdout)
   ap=subprocess.run(['git','apply','--unsafe-paths','--directory',str(root),str((p.parent/'LPi_harness.patch').resolve())],capture_output=True,text=True)
   if ap.returncode:errors.append([a,'patch apply',ap.stderr]);continue
   for f,h in r['source_hashes'].items():
    q=root/f.removeprefix('LPi_src/')
    if not q.is_file() or hashlib.sha256(q.read_bytes()).hexdigest()!=h:errors.append([a,'reconstructed source hash',f])
for p in sorted(Path('lean').glob('LPi_*.lean')):
 r=latest.get(p.stem)
 if not r:errors.append([p.name,'no passing module']);continue
 if hashlib.sha256(p.read_bytes()).hexdigest() not in r['source_hashes'].values():errors.append([p.name,'not successful snapshot'])
 if re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option\s+max(?:Heartbeats|RecDepth)',p.read_text()):errors.append([p.name,'forbidden source'])
assert len(lean)<=60 and len(kani)<=30
for name in ['FJv_Top','ARX_Root']:
 before=(E/f'LPi_{name}_BEFORE.lean.txt').read_bytes();after=Path('lean',name+'.lean').read_bytes();(E/f'LPi_{name}_AFTER.lean.txt').write_bytes(after)
 if before!=after:errors.append([name,'headline source changed'])
result={'errors':errors,'lean_compiles':len(lean),'lean_pass':sum(r['exit_status']==0 for r in lean),'kani_runs':len(kani),'kani_pass':sum(r['exit_status']==0 for r in kani),'accepted_new_modules':sorted(n for n in latest if n.startswith('LPi_')),'excluded_failed_extra':'LPi_L061/LPi_PowersWitness; entire file excluded','top_premises_removed':0,'delta':{'T':0,'P':0,'G':0},'baseline':'83T/3P/13G inherited, no fresh absolute recount','full_release_replay':False,'source_to_elf':'retained/open; no shipped change'}
(E/'LPi_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));assert not errors
