"""Independent final local source/text/hash audit. No operational imports."""
import ast,hashlib,json,pathlib,resource,subprocess,sys,time,traceback
START=time.monotonic();H=pathlib.Path(__file__).resolve().parent;O=H.parents[1]/'evidence/sbf-finite-probe-20261025'
checks=[];inputs={}
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(ok,label):
 checks.append(dict(check=label,passed=bool(ok)))
 if not ok:raise AssertionError(label)
def git(rev,path):
 b=subprocess.check_output(['git','show',rev+':'+path]);inputs[rev+':'+path]=pin(b);return b
def values(p):
 t=ast.parse(p.read_bytes());return {n.targets[0].id:ast.literal_eval(n.value) for n in t.body if isinstance(n,ast.Assign)}
exit=0;failure=None
try:
 base='evidence/sbf-runtime-acquire-20261025/'
 candidate_raw=git('fe20884963',base+'SbfRuntimeAcquire-candidate-INPUT-DATA-ONLY.json');candidate=json.loads(candidate_raw)
 check(pin(candidate_raw)==dict(size=30423,sha256='c69379a1f6086d66925d0ab14824a9f1c39d1a8789f8f47c8c9d183e01aa2f24'),'accepted exact30423B candidate')
 integration=json.loads(git('fe20884963',base+'SbfRuntimeAcquire-NEXT-FINITE-PROBE-INTEGRATION.json'))
 raw=git('fe20884963',base+'SbfRuntimeAcquire-transport.stdout');captured=json.loads(raw)
 plan=git('fe20884963',base+'SbfRuntimeAcquire-plan.json')
 payload=git('fe20884963','tools/sbf-runtime-acquire-20261025/SbfRuntimeAcquire_payload.py.txt')
 for b,p,label in [(raw,integration['raw_data'],'raw'),(plan,integration['plan'],'plan'),(payload,integration['payload'],'payload')]:check(pin(b)==p,'complete immutable '+label+' pin')
 lead=json.loads(git('86d9ae90c6','evidence/lead-review-20261025/sbf-runtime-acquire-v1.json'))
 check(lead['revision']=='fe20884963' and lead['exit_status']==0,'independent lead review reused only')
 fixed=values(H/'SbfFinite_fixed.py');runtime=fixed['RUNTIME'];catalog=fixed['CATALOG']
 expected=dict(candidate['manifest'],version='SbfFiniteLinux-tiny-v1',root='/var/lib/SbfFinite-20261025-v1/rootfs')
 expected['files']=[dict(r,physical=expected['root']+r['logical']) for r in candidate['manifest']['files']]
 check(runtime==expected,'complete runtime has ONLY explicit root/version/destination mapping deltas')
 check(tuple(runtime['argv'])==fixed['ARGV']==tuple(candidate['manifest']['argv']),'captured argv/body unchanged byte-for-byte')
 check(runtime['env']==fixed['ENV']==candidate['manifest']['env'],'exact captured environment')
 check(len(catalog)==92 and sum(r['source']['size'] for r in catalog)==35655597,'all92 clone bytes counted')
 check(len({r['source']['physical'] for r in catalog})==82,'82 physical endpoints')
 for original,row in zip(candidate['manifest']['files'],catalog):
  source=captured['outcomes'].get(original['logical'],captured['files'][original['physical']])
  if source.get('physical')!=original['physical']:source=captured['files'][original['physical']]
  check(row==dict(guest=original['logical'],destination=expected['root']+original['logical'],mode=original['mode'],source=source),'complete exact captured source row '+original['logical'])
 check((H/'SbfFiniteRss_reviewed.json').read_bytes()==git('20a0f5bb38','tools/sbf-producer-20261025/SbfProducerRss_reviewed.json'),'full RssGOv3 policy source bundle byte-identical')
 identities=json.loads((O/'SbfFinite-statements-and-identities.json').read_bytes())
 for n,row in identities.items():
  if n.startswith('9f50:'):
   origin=n.split(':',1)[1];check(pin(git('9f50be799e','tools/sbf-linux-20261025/'+origin))==row['source'],'immutable9f50 lineage '+origin)
  else:check(pin((H/n).read_bytes())==row['after'],'final delta target '+n)
 inventory=values(H/'SbfFinite_inventory.py')['PACKAGE_CATALOG']
 package_pins=values(H/'SbfFinite_package_pins.py')['FILES']
 for r in inventory:check(pin(r['payload'])=={k:r['pin'][k] for k in ('size','sha256')}==pin((H/r['name']).read_bytes()),'fresh literal package payload '+r['name'])
 check(len(inventory)+92<=256 and sum(r['pin']['size'] for r in inventory)+35655597<=64*2**20,'global setup count/byte bounds')
 names={r['name'] for r in inventory};bootstrap={'SbfFinite_entry.py','SbfFinite_user_entry.py','SbfFinite_package_pins.py'}
 check(set(package_pins)==names-bootstrap,'noncircular package pin partition')
 imports={}
 for name in names|{'SbfFinite_install.py','SbfFinite_inventory.py','SbfFinite_install_entry.py'}:
  if not name.endswith('.py'):continue
  t=ast.parse((H/name).read_bytes());first=t.body[0]
  check(isinstance(first,ast.Raise) or (isinstance(first,ast.If) and ast.unparse(first.test)=="__name__ == '__main__'" and isinstance(first.body[0],ast.Raise)),'public denial before imports '+name)
  deps={}
  for n in ast.walk(t):
   if isinstance(n,ast.Import):
    for a in n.names:deps[a.name]=True
   if isinstance(n,ast.ImportFrom):deps[n.module]=True
  imports[name]=sorted(deps)
  for n in deps:
   if n.startswith('SbfFinite'):check(n+'.py' in names|{'SbfFinite_install.py','SbfFinite_inventory.py'},'finite source import closure '+name+'->'+n)
 for entry in ('SbfFinite_entry.py','SbfFinite_user_entry.py','SbfFinite_install_entry.py'):
  v=values(H/entry)
  check(entry not in v['SbfFinite_PINS'],'entry selfpin remains external '+entry)
  for name,p in v['SbfFinite_PINS'].items():check(pin((H/name).read_bytes())==p,'literal dormant entry pin '+entry+'->'+name)
 receipt=json.loads((O/'SbfFinite-tests-attempt8.json').read_bytes())
 for p in sorted(H.iterdir()):
  if p.is_file() and p.name in receipt['source_overlay'] and p.name!='SbfFinite_REVIEW.md':check(pin(p.read_bytes())==receipt['source_overlay'][p.name],'tested final source overlay '+p.name)
 check(receipt['exit']==0 and receipt['tests']==30,'30 final synthetic methods passed, no native effects inferred')
except BaseException:exit=1;failure=traceback.format_exc()
r=resource.getrusage(resource.RUSAGE_SELF);rss=r.ru_maxrss*(1 if sys.platform=='darwin' else 1024)
children=resource.getrusage(resource.RUSAGE_CHILDREN);child_rss=children.ru_maxrss*(1 if sys.platform=='darwin' else 1024)
check(rss<512*2**20,'source validation below512MiB')
report=dict(command=getattr(sys,'orig_argv',sys.argv),target='fixed final immutable-source and import/pin audit',exit=exit,wall_seconds=time.monotonic()-START,
 peak_process_rss_bytes=rss,peak_aggregate_rss_bytes=None,aggregate_peak_upper_bound_bytes=rss+child_rss,
 aggregate_method='Exact concurrent aggregate peak UNOBSERVED; conservative sum of SELF/CHILDREN peak RSS, Git reads serial and only children',
 child_peak_rss_bytes=child_rss,child_swaps=children.ru_nswap,
 swap=r.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),
 source_overlay={p.name:pin(p.read_bytes()) for p in sorted(H.iterdir()) if p.is_file()},immutable_inputs=inputs,
 dependencies={n:dict(path=m.__file__,**pin(pathlib.Path(m.__file__).read_bytes())) for n,m in sorted(sys.modules.items()) if getattr(m,'__file__',None) and pathlib.Path(m.__file__).is_file()},
 interpreter=dict(path=sys.executable,version=sys.version,**pin(pathlib.Path(sys.executable).read_bytes())),checks=checks,source_imports=locals().get('imports',{}),failure=failure,
 axioms='N/A; no Lean/theorem/compiler/native audit',actual_native_host_root_install_probe_calls=0,derived_JSON_over5MB=[])
i=1
while (O/('SbfFinite-final-check'+str(i)+'.json')).exists():i+=1
(O/('SbfFinite-final-check'+str(i)+'.json')).write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
print(json.dumps(dict(exit=exit,checks=len(checks),rss=rss,failure=failure)));raise SystemExit(exit)
