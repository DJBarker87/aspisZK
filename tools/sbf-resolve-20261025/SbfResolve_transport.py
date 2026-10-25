import hashlib,json,pathlib,resource,shlex,subprocess,sys,time
B=pathlib.Path('evidence/sbf-resolve-20261025');T=pathlib.Path('tools/sbf-resolve-20261025');REV='65c4082110';S='/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024';PL='/home/dombarker/.cache/solana/v1.52/platform-tools/'
def git(p):return subprocess.check_output(['git','show',REV+':'+p])
op=sys.argv[1];src=(T/'SbfResolve_host.py').read_text();rev=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()
req=dict(operation=op,revision=rev,helper_sha256=hashlib.sha256(src.encode()).hexdigest(),host_command=['/usr/bin/python3','-I','-S','-B','-c',src])
a=json.loads(git('evidence/sbf-recapture-prep-20261024/archive-members.json'));req['tool_pins']={PL+r['path']:r['archive_sha256'] for r in a if r['path'] in ['rust/bin/cargo','rust/bin/rustc']};req['tool_pins']['/usr/bin/strace']='28f957c227012de0b18d1bd7fff2d396cb693ea60ed8013be68de071e84b5001'
if op=='init':
 f=json.loads(git('evidence/sbf-inputs-20261024/finish.stdout.json'));req['indices']={r['path']:r for r in f['index_rows']};r=f['public_config'];req['indices'][r['path'].split('/SbfInputs-20261024-v3/')[1]]=r
 manifests=json.loads(git('evidence/sbf-closure-20261025/static-inputs.json'))['manifest_documents'];material=json.loads(git('evidence/sbf-recapture-prep-20261024/materialized-files.json'));req['manifests']=[r for r in material if r['path'].removeprefix('src/') in manifests or r['path'] in ['src/Cargo.lock','src/.cargo/config.toml']]
 assert len(req['manifests'])==19
 req['helpers']={n:(T/n).read_text() for n in ['SbfResolve_guard.py','SbfResolve_host.py']}
if op=='query':
 req['number']=int(sys.argv[2]);objects=json.loads(git('evidence/sbf-closure-20261025/static-dso-closure.json'))['objects'];runtime={}
 for name in [PL+'rust/bin/cargo',PL+'rust/bin/rustc',PL+'rust/lib/librustc_driver-26fee09958747c28.so','/usr/bin/python3.12']:
  obj=objects[name];runtime[name]=obj['sha256']
  for row in obj['resolved'].values():runtime[row['resolved']]=row['sha256']
 for r in a:
  if r['path']=='rust/lib/librustc_driver-26fee09958747c28.so':runtime[PL+r['path']]=r['archive_sha256']
 req['runtime_pins']=runtime
argv=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90',' '.join(shlex.quote(x) for x in req['host_command'])]
label=op+('-'+str(req['number']) if op=='query' else '')
if len(sys.argv)>2 and op=='universe':label+='-'+sys.argv[2];req['receipt_name']=label+'-receipt.json'
request=(json.dumps(req,sort_keys=True)+'\n').encode();(B/('SbfResolve-'+label+'-request.json')).write_bytes(request)
t=time.monotonic();p=subprocess.run(argv,input=request,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=600)
for name,b in [('stdout',p.stdout),('stderr',p.stderr)]:
 assert len(b)<5_000_000
 (B/('SbfResolve-'+label+'.'+name)).write_bytes(b)
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN);receipt=dict(transport=argv,request_sha256=hashlib.sha256(request).hexdigest(),request_bytes=len(request),exit=p.returncode,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swap=u.ru_nswap+c.ru_nswap,source_revision=rev,print_axioms='N/A',stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest())
(B/('SbfResolve-'+label+'-transport.json')).write_text(json.dumps(receipt,indent=2)+'\n')
try:
 j=json.loads(p.stdout);print(json.dumps({k:v for k,v in j.items() if k not in ['host_command','source_pins','source_pins_after','locked_universe','tools_before','tools_after','runtime_before','runtime_after','parent_pins','parent_pins_before','parent_pins_after','metadata_summary']},indent=2)[:12000]);
 if 'metadata_summary' in j:print(json.dumps(j['metadata_summary'],indent=2)[:12000])
except Exception:print(p.stdout[:3000].decode(errors='replace'));print(p.stderr[:3000].decode(errors='replace'))
sys.exit(p.returncode)
