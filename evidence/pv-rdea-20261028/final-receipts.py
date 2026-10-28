from pathlib import Path
import json,re,hashlib,subprocess
D=Path(__file__).parent;ROOT=D.resolve().parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def timing(p):
 s=p.read_text() if p.exists() else '';ans={}
 for label,k in [('Elapsed (wall clock) time (h:mm:ss or m:ss)','wall_time'),('Maximum resident set size (kbytes)','peak_rss_KiB'),('Swaps','swaps'),('Exit status','exit_status')]:
  m=re.search(re.escape(label)+r':\s*(.*)',s);ans[k]=m[1] if m else None
 return ans
sources={p.stem:str(p) for p in Path('docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RDEA_*.lean')}
for x in json.loads((D/'actual-source-closure.json').read_text())['modules']:sources[x['module'].split('.')[-1]]=x['path']
version_cache={}
def authority(path,digest):
 if path not in version_cache:
  vv=[]
  commits=subprocess.check_output(['git','log','--format=%H','HEAD','--',path],text=True).splitlines()
  for rev in commits:
   r=subprocess.run(['git','show',rev+':'+path],capture_output=True)
   if r.returncode==0:vv.append((sha(r.stdout),rev))
  version_cache[path]=vv
 for h,rev in version_cache[path]:
  if h==digest:
   return dict(source_revision=rev,source_blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip())
 return dict(source_revision=None,source_blob=None,revision_note='Exact bytes identified by launcher SHA; no matching tracked source revision found. No successful theorem credit from a failed attempt.')
rows=[]
for i in range(60300,60400):
 out=D/f'out-{i}.log';sf=D/f'sha-{i}.txt';tm=D/f'time-{i}.log'
 if not out.exists():continue
 txt=out.read_text();line=sf.read_text().strip() if sf.exists() else '';parts=line.split(maxsplit=1);digest=parts[0] if parts else None
 module=Path(parts[1]).stem if len(parts)>1 else None;path=sources.get(module)
 t=timing(tm);status=t['exit_status'];err=[x for x in txt.splitlines() if 'error:' in x or 'error(' in x]
 axioms=[x for x in txt.splitlines() if 'depends on axioms:' in x or 'does not depend on any axioms' in x]
 ok=status=='0' and not err and not any('sorryAx' in x for x in axioms)
 row=dict(attempt=i,target='R1Z.'+module if module else None,source_path=path,source_sha256=digest,**t,credited_proof=ok,operationally_compliant=i!=60309,print_axioms=axioms,errors=err,caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000),cohort='private coherent actual-source prefix' if i in range(60340,60380) or i in [60385,60386,60387,60388,60389,60390,60391,60392,60393,60399] else 'standing env-J physical prefix')
 if path and digest:row.update(authority(path,digest))
 if not axioms:row['print_axioms_note']='N/A: source/definition dependency compilation or pre-elaboration failure; see exact target and status'
 row['command']='run2.py private-env-J.json actual-objects actual-sources TARGET.olean SOURCE.lean 7000' if row['cohort'].startswith('private') else f'run-joint.sh {i} R1Z/{module} J 7000 8'
 rows.append(row)
(D/'attempts.json').write_text(json.dumps(rows,indent=2)+'\n')
assert len(rows)<=100
# Native names are recorded scopes, including conservative charges for barrier-only refusals.
native=[]
for name in ['native01','build','build03','build04','build04-retry','inventory','machine-inventory','machine-relocations','stdlib-ir','ir-linked-inventory','stdlib-inlined-sites','root-preopt','stdlib-inlined-sites-v2','site-reconciliation','stdlib-callers','machine-stdlib-callers','runtime-unit-closure','diagnostic-source-pins','collect-receipts']:
 t=D/(name+'-time.log')
 if not t.exists():
  alt={'build04-retry':'build04-time.log','native01':'native01-time.log'}.get(name)
  if alt:t=D/alt
 barrier=D/(name+'-barrier.json');bj=json.loads(barrier.read_text()) if barrier.exists() else None
 native.append(dict(scope=name,**timing(t),barrier_allowed=bj.get('allowed') if bj else None,limits=bj.get('own_limits') if bj else None,source_revision='713a92729abc0bb55677dd2ea7d2107490b5cd24' if name.startswith('build') or name=='root-preopt' else 'scripts pinned in current evidence directory',print_axioms='N/A: native/read-only analysis',note='Internal barrier refused before compiler; conservatively charged scope' if name=='build04' else None))
(D/'native-scopes.json').write_text(json.dumps(native,indent=2)+'\n')
summary=dict(lean_attempts=len(rows),lean_success=sum(x['credited_proof'] for x in rows),lean_failed=sum(not x['credited_proof'] for x in rows),native_scopes_conservatively_charged=len(native),kani=0,missing_source_revision=[x['attempt'] for x in rows if x.get('source_revision') is None],peak_lean_rss_KiB=max(int(x['peak_rss_KiB']) for x in rows if x['peak_rss_KiB']),swaps=sum(int(x['swaps']) for x in rows if x['swaps']))
(D/'final-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
