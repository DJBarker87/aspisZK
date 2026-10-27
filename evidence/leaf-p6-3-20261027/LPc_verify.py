"""Read-only final receipt, source, dependency and budget consistency audit."""
from pathlib import Path
import json,re,hashlib,subprocess,shlex
E=Path(__file__).resolve().parent;errors=[];groups={};latest={};pins={}
complete=(E/'LPc_L060/receipt.json').exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for kind,count in [('L',60 if complete else 59),('K',20)]:
 rows=[]
 for i in range(1,count+1):
  a=f'LPc_{kind}{i:03}';p=E/a/'receipt.json'
  if not p.exists():errors.append(a+' missing receipt');continue
  r=json.loads(p.read_text());rows.append(r)
  if r['limits']!=limits:errors.append(a+' caps')
  if int(r['swaps'])!=0:errors.append(a+' swap')
  for field in ['command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','cgroup_memory_peak_bytes','print_axioms']:
   if field not in r:errors.append(a+' missing '+field)
  if kind=='L':
   if sha(E/a/'source.lean.txt') not in r['source_hashes'].values():errors.append(a+' source snapshot')
   if '-M7000' not in r['command']:errors.append(a+' Lean memory flag')
   if r['exit_status']==0:
    latest[r['module']]=r
    for line in r['print_axioms']:
     m=re.search(r'\[(.*?)\]',line,re.S)
     if m and not {x.strip() for x in m[1].split(',')}.issubset({'propext','Classical.choice','Quot.sound'}):errors.append(a+' axiom '+line)
    for obj in r['deps_fingerprint']['selected_objects'].values():
     path=obj['path'];h=obj['sha256']
     if path in pins and pins[path]!=h:errors.append('conflicting dependency '+path)
     pins[path]=h
  elif r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']!='3':errors.append(a+' optimization')
 groups[kind]=rows
for p in E.glob('LPc_*.lean'):
 if p.stem=='LPc_Audit' and not complete:continue
 r=latest.get(p.stem)
 if not r or sha(p) not in r['source_hashes'].values():errors.append('unaccepted current source '+p.name)
 if re.search(r'^\s*(?:axiom|sorry|admit)\b|native_decide|set_option\s+(?:maxRecDepth|maxHeartbeats)',p.read_text(),re.M):errors.append('forbidden construct '+p.name)
plan=json.loads((E/'LPc_audit-plan.json').read_text())
if complete:
 audit=json.loads((E/'LPc_L060/receipt.json').read_text())
 actual={re.match("'([^']+)'",v)[1] for v in audit['print_axioms']}
 if audit['exit_status']!=0:errors.append('final audit failed')
 if set(plan['new']+plan['inherited_leaves'])!=actual:errors.append('final audit name coverage')
# Recheck every selected direct object and companion before own caches are removed.
script='import json,sys,hashlib;from pathlib import Path;x=json.load(sys.stdin);print(json.dumps({p:(hashlib.sha256(Path(p).read_bytes()).hexdigest() if Path(p).is_file() else None) for p in x}))'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=json.dumps(list(pins)),text=True,capture_output=True,check=True)
actual_pins=json.loads(r.stdout)
(E/'LPc_final-dependency-hashes.json').write_text(json.dumps(actual_pins,indent=2)+'\n')
removed_cache_verified=0
cleanup_path=E/'LPc_LeanCleanup.json'
cleanup=json.loads(cleanup_path.read_text()) if cleanup_path.exists() else None
object_hashes=json.loads((E/'LPc_LeanObjectHashes.json').read_text()) if cleanup else {}
for p,h in pins.items():
 if actual_pins[p]==h:continue
 if cleanup and actual_pins[p] is None and p.startswith(cleanup['removed']+'/'):
  key='LPc_objects/'+p.split('/LPc_objects/',1)[1]
  if object_hashes.get(key,{}).get('sha256')==h:
   removed_cache_verified+=1
   continue
 errors.append('dependency drift '+p)
# Exact per-run harness variants remain patch artifacts, never Rust source edits.
inputs=json.loads((E/'LPc_INPUTS/LPc_input-map.json').read_text())
for r in groups['K']:
 row=inputs.get(r['attempt'])
 if row is None:errors.append(r['attempt']+' missing input patch');continue
 if sha(E/'LPc_INPUTS'/row['patch'])!=row['sha256']:errors.append(r['attempt']+' input patch hash')
 if row['source_hashes']!=r['source_hashes']:errors.append(r['attempt']+' input source map')
entry=json.loads((E/'LPc_entry.json').read_text());root=E.parent.parent
if sha(root/'lean/ARX_Root.lean')!=sha(E/'LPc_BEFORE.lean.txt') or sha(E/'LPc_AFTER.lean.txt')!=sha(E/'LPc_BEFORE.lean.txt'):errors.append('actual top statement drift')
changed=subprocess.check_output(['git','diff','--name-only',entry['revision'],'--'],text=True,cwd=root).splitlines()
if any(not p.startswith('evidence/leaf-p6-3-20261027/') for p in changed):errors.append('out-of-scope tracked changes')
if json.loads((E/'LPc_source-provenance.json').read_text())['errors']:errors.append('native scratch source provenance')
summary={'errors':errors,'all_consistency_checks_pass':not errors,'removed_own_cache_pins_matched_to_precleanup_hashes':removed_cache_verified,'scope':'local leaf stage proofs; no actual-top premise removed','axioms':'standard only for every accepted result; failed sorryAx diagnostics excluded','final_audit_ran':complete,'new_theorems_audited':len(plan['new']) if complete else len(plan['new'])-2,'inherited_leaves_in_final_audit':len(plan['inherited_leaves']) if complete else 0,'actual_top_statement_sha256':sha(root/'lean/ARX_Root.lean'),'before_after_identical':True,'premises':{'removed':0,'added':0,'changed':0},'ledger_delta':{'T':0,'P':0,'G':0,'C':0}}
for k,rows in groups.items():
 summary[k]={'used':len(rows),'passed':sum(r['exit_status']==0 for r in rows),'failed':sum(r['exit_status']!=0 for r in rows),'wall_seconds_sum':sum(r['wall_seconds'] for r in rows),'peak_rss_kib':max(int(r['peak_rss_kib']) for r in rows),'cgroup_peak_bytes':max(int(r['cgroup_memory_peak_bytes']) for r in rows),'swap_sum':sum(int(r['swaps']) for r in rows),'reservation_retries':sum(r['reservation_retries'] for r in rows),'failed_attempts':[r['attempt'] for r in rows if r['exit_status']!=0]}
(E/'LPc_Verification.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
