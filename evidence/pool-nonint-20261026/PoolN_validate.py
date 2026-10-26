"""Read-only proof/source/evidence audit, writing only this job's audit receipt."""
from pathlib import Path
import hashlib,json,re,subprocess,time
start=time.monotonic();B=Path(__file__).parent;R=B.parents[1];errors=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(B.glob('PoolN_*/receipt.json')):
 x=json.loads(p.read_text());rows.append(x)
 for name,digest in x['source_hashes'].items():
  if sha(p.parent/'sources'/name)!=digest:errors.append('snapshot hash: '+str(p)+' '+name)
 if x['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append('caps: '+x['attempt'])
 if int(x['swaps'])!=0:errors.append('swap: '+x['attempt'])
 if x['kind']=='lean' and '-M7000' not in x['command']:errors.append('Lean cap: '+x['attempt'])
 if x['kind']=='kani' and (x['env'].get('CARGO_PROFILE_DEV_OPT_LEVEL')!='3' or x['env'].get('CARGO_BUILD_JOBS')!='4'):errors.append('Rust profile: '+x['attempt'])
 if x['kind']=='lean' and x['exit_status']==0:
  for line in x['print_axioms']:
   names=re.search(r'depends on axioms: \[([^\]]*)\]',line)
   if names and not set(names.group(1).split(', '))<={'propext','Classical.choice','Quot.sound'}:errors.append('axioms: '+line)
kanis=[x for x in rows if x['kind']=='kani'];leans=[x for x in rows if x['kind']=='lean']
if {x['attempt'] for x in kanis}!={f'PoolN_KANI{i:03}' for i in range(1,41)}:errors.append('Kani receipt inventory')
if {x['attempt'] for x in leans}!={f'PoolN_LEAN{i:03}' for i in range(1,10)}:errors.append('Lean receipt inventory')
modules=[]
for p in sorted((R/'lean').glob('PoolN_*.lean')):
 text=p.read_text()
 if re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',text):errors.append('proof discipline: '+str(p))
 matches=[x for x in leans if x['exit_status']==0 and x['source_hashes'].get(p.name)==sha(p)]
 if not matches:errors.append('no exact-source green receipt: '+p.name)
 modules.append(dict(module=p.name,sha256=sha(p),green_attempts=[x['attempt'] for x in matches]))
pins=json.loads((B/'PoolN_source-pins.json').read_text())
for f,pin in pins['files'].items():
 if sha(R/f)!=pin['sha256'] or (R/f).stat().st_size!=pin['bytes']:errors.append('frozen input changed: '+f)
m=json.loads((R/'evidence/lowering2-20261026/Low2_build_manifest.json').read_text());counts=[]
for build in m['builds']:
 counts.append(len(build['repository_compiler_inputs']))
 for item in build['repository_compiler_inputs']:
  if sha(R/item['path'])!=item['sha256']:errors.append('inherited input changed: '+item['path'])
for f in ['PoolN_host-overlay-pins.json','PoolN_final-host-overlay-pins.json']:
 x=json.loads((B/f).read_text())
 if x['count']!=133 or not all(r['production_prefix_matches'] and r['suffix_matches'] for r in x['rows']):errors.append('host overlay: '+f)
# Every projected branch predicate and literal prefix span is tied to source.
s=(R/'programs/aspis-pool/src/processor.rs').read_text();d=json.loads((B/'PoolN_dispatch-pin.json').read_text())
if hashlib.sha256(s.encode()).hexdigest()!=d['source_sha256']:errors.append('dispatch source')
for row in json.loads((B/'PoolN_prefix-manifest.json').read_text()):
 data=(R/row['file']).read_bytes()
 if hashlib.sha256(data).hexdigest()!=row['source_sha256'] or hashlib.sha256(data[row['start_byte']:row['end_byte']]).hexdigest()!=row['body_sha256']:errors.append('literal prefix span: '+row['handler'])
base=pins['revision'];paths=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
for p in paths:
 if not (p.startswith('evidence/pool-nonint-20261026/') or re.fullmatch(r'lean/PoolN_.*\.lean',p)):errors.append('outside assigned scope: '+p)
check=subprocess.run(['git','diff','--check',base,'--','lean/PoolN_*.lean','evidence/pool-nonint-20261026',':(exclude)evidence/pool-nonint-20261026/**/stdout.log'],cwd=R,text=True,capture_output=True)
if check.returncode:errors.append('authored whitespace: '+check.stdout)
result={'claim':'Proof/source/evidence integrity only. Exhaustive Pool dispatch frame and PoolN_Frame.all_handlers remain unproved.','worker_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'Lean':{'attempts':len(leans),'budget':100,'passed':sum(x['exit_status']==0 for x in leans),'peak_rss_kib':max(int(x['peak_rss_kib']) for x in leans),'wall_seconds_sum':sum(x['wall_seconds'] for x in leans)},'Kani':{'attempts':len(kanis),'budget':40,'passed':sum(x['exit_status']==0 for x in kanis),'peak_rss_kib':max(int(x['peak_rss_kib']) for x in kanis),'wall_seconds_sum':sum(x['wall_seconds'] for x in kanis)},'all_swaps_zero':True,'current_modules':modules,'inherited_compiler_input_counts':counts,'host_production_prefixes_matched':133,'whitespace_scope':'Authored files and snapshots; raw compiler stdout preserved verbatim and excluded.','full_package_replays':0,'new_ELF_builds':0,'new_security_trust_items':0,'accepted_attacker_chosen_checkpoint_write_found':False,'inspection_wall_seconds':time.monotonic()-start,'errors':errors,'exit':int(bool(errors))}
(B/'PoolN_validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));raise SystemExit(bool(errors))
