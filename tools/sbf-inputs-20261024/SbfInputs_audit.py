#!/usr/bin/env python3
"""Focused offline receipt/manifest/plan audit; no host reads or build execution."""
import hashlib,json,pathlib,resource,subprocess,sys,time
start=time.monotonic();E=pathlib.Path('evidence/sbf-inputs-20261024');T=pathlib.Path('tools/sbf-inputs-20261024');checks=[]
# Preserve any new failure with process metrics, without rerunning unchanged inputs.
def failure(tp,value,tb):
 import traceback
 u=resource.getrusage(0);r=dict(command=[sys.executable,"-B",__file__],source_revision=subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip(),script_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),exit=1,error=repr(value),traceback="".join(traceback.format_exception(tp,value,tb)),wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,print_axioms="N/A")
 with (E/"audit-failed-v2.json").open("x") as f:json.dump(r,f,indent=2);f.write("\n")
 traceback.print_exception(tp,value,tb)
sys.excepthook=failure
def sha(b):return hashlib.sha256(b).hexdigest()
def read(name):return json.loads((E/name).read_text())
def check(name,condition):
 assert condition,name
 checks.append(name)
prep=read('prepare.stdout.json');p=read('preparation.json');f=read('finish.stdout.json');plan=read('future-plan.json')
for prefix in ['prepare','finish','prepare-v1','prepare-v2']:
 tr=read(prefix+'.transport.json');raw=(E/(prefix+'.stdout.json')).read_bytes();err=(E/(prefix+'.stderr.txt')).read_bytes();x=json.loads(raw)
 check(prefix+' stdout/stderr seal',sha(raw)==tr['stdout_sha256'] and sha(err)==tr['stderr_sha256'])
 check(prefix+' command binding',tr['command'][:2]==['ssh','-o'] and tr['exit']==x['exit'])
 source=tr['helper_sha256'];check(prefix+' retained literal helper',any(sha(q.read_bytes())==source for q in T.glob('SbfInputs*')))
 check(prefix+' source revision association',x['source_revision']==tr['source_revision'])
 check(prefix+' metrics/axioms',x['wall_seconds']>=0 and x['peak_rss_kib']>0 and x['swap']==0 and x['print_axioms'].startswith('N/A'))
 check(prefix+' committed helper before host operation',source==sha(subprocess.check_output(['git','show',tr['source_revision']+':tools/sbf-inputs-20261024/'+('SbfInputs_finish_host.py' if prefix=='finish' else 'SbfInputs_prepare.py')])))
check('new preparation success only',prep['exit']==f['exit']==0 and read('prepare-v1.stdout.json')['exit']==read('prepare-v2.stdout.json')['exit']==1)
for key,name in [('output','preparation.json'),('manifest','registry-files.jsonl')]:
 b=(E/name).read_bytes();check(name+' collection seal',len(b)==prep[key]['bytes'] and sha(b)==prep[key]['sha256'])
packages=read('packages.json');check('123 exact selected package identities',{x['crate'] for x in p['packages']}=={x['crate'] for x in packages} and len(packages)==123)
check('archives lock checksums',all(x['archive_sha256']==x['lock_checksum'] for x in packages) and all(a['archive']['sha256']==b['archive_sha256'] for a,b in zip(p['packages'],packages)))
rows=[json.loads(line) for line in (E/'registry-files.jsonl').read_text().splitlines()];regular=[r for r in rows if r['type']=='regular'];dirs=[r for r in rows if r['type']=='directory']
check('manifest unique exact paths',len({r['path'] for r in rows})==len(rows) and all(not pathlib.PurePosixPath(r['path']).is_absolute() and '..' not in pathlib.PurePosixPath(r['path']).parts for r in rows))
check('manifest ordinary types/modes',len(rows)==len(regular)+len(dirs) and all(int(r['mode'],8)&~0o777==0 for r in rows))
check('2950 files 28788833 bytes',len(regular)==p['files']==2950 and sum(r['bytes'] for r in regular)==p['bytes']==28788833)
check('published2704 archives123 markers123',sum(x['source_files'] for x in p['packages'])==2704 and len([r for r in regular if r['path'].endswith('.crate')])==123 and len([r for r in regular if 'generated' in r])==123)
for pkg in p['packages']:
 root='cargo/registry/src/'+pkg['index']+'/'+pkg['crate']+'/'
 rr=[r for r in regular if r['path'].startswith(root)];check(pkg['crate']+' source exact recorded set',pkg['exact_set'] and len(rr)==pkg['source_files']+1)
 marker=[r for r in rr if r['path']==root+'.cargo-ok'];check(pkg['crate']+' official metadata distinction',len(marker)==1 and marker[0]['sha256']==sha(b'{"v":1}') and 'generated' in marker[0])
check('118 public index files for123 selected versions',f['index_files']==118 and len(f['index_rows'])==123 and {r['crate'] for r in f['index_rows']}=={r['crate'] for r in packages})
lookup={x['crate']:x['archive_sha256'] for x in packages};check('index checksum matches archives',all(r['locked_entry_checksum']==lookup[r['crate']] for r in f['index_rows']))
check('namespace denied retained',f['namespace_probe']['exit']==1 and 'Operation not permitted' in f['namespace_probe']['stderr'] and not f['namespace_probe']['stdout'])
check('probe same tested literal',read('finish-tests.json')['namespace_executed']==False and {pathlib.Path(k).name:v for k,v in read('finish-tests.json')['inputs'].items()}['SbfInputs_finish_host.py']==f['helper_sha256'])
oldrev='ed3227f4dae529ed61d7f63c9dbd5adb8028e953'
for b in plan['builds']:
 mode=b['mode'];name=f'docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023/build-{mode}-v1/command.json';raw=subprocess.check_output(['git','show',oldrev+':'+name]);old=json.loads(raw)
 check(mode+' exact original argv',b['command']==old['command'])
 check(mode+' original explicit env retained',all(b['environment'][k]==v for k,v in old['env'].items()))
 check(mode+' -j4 and wrapper retained',b['command'][b['command'].index('-j')+1]=='4' and b['environment']['CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS']=='-C link-arg=--threads=4')
 check(mode+' no execution authorization','BLOCKED' in b['status'])
check('fixed current ELF pins',[b['expected_sha256'] for b in plan['builds']]==['f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'])
check('future3G4G proposal not grant',plan['resources']['proposal_only'] and plan['resources']['MemoryHigh']=='3G' and plan['resources']['MemoryMax']=='4G' and plan['resources']['MemorySwapMax']==0 and plan['resources']['TasksMax']==64)
check('zero budgets',all(x==0 for x in plan['budgets'].values()))
check('all derived JSON under5MB',all(q.stat().st_size<=5_000_000 for q in E.glob('*.json')))
changed=subprocess.check_output(['git','diff','--name-only',oldrev,'HEAD'],text=True).splitlines();check('pathlimited committed changes',all(x.startswith(('tools/sbf-inputs-20261024/','evidence/sbf-inputs-20261024/')) for x in changed))
for row in read('reused-inputs.json'):
 b=subprocess.check_output(['git','show',row['revision']+':'+row['path']]);check('reuse '+row['path'],sha(b)==row['sha256'] and len(b)==row['bytes'])
# This is a NEW local interpreter observation, not retroactive per-operation DSO evidence.
runtime={};exe=pathlib.Path(sys.executable).resolve();runtime[str(exe)]=dict(bytes=exe.stat().st_size,sha256=sha(exe.read_bytes()),version=sys.version)
u=resource.getrusage(0);out=dict(command=[sys.executable,'-B',__file__],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=sha(pathlib.Path(__file__).read_bytes()),inputs={q.name:dict(bytes=q.stat().st_size,sha256=sha(q.read_bytes())) for q in E.iterdir() if q.is_file()},exit=0,checks=checks,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,print_axioms='N/A: no Lean theorem/import or compiler executed',runtime=runtime,claim='Focused offline consistency only. No input TOU, namespace/mount readiness, compiler correctness, historical warm provenance or security closure.',assumptions=dict(discharged=['new private registry archive/lock/checksum/source-set associations','exact original three-command proposal','namespace feasibility tested and blocked'],retained=plan['blockers']+['native primitive/Std/P7/source/model/extraction/effect/release joins','both security targets NOT YET ESTABLISHED'],new_trust=[],premise_changes='none; before=after/N/A'))
with (E/'audit.json').open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({k:v for k,v in out.items() if k in ('exit','wall_seconds','peak_rss_bytes','swap','print_axioms')}));print(str(len(checks))+' focused checks passed')
