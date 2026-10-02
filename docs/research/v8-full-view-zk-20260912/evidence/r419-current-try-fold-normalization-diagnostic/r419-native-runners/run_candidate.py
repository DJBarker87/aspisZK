"""Apply the inspected native tool to a fresh COPY for audit, not translation."""
import datetime, hashlib, json, pathlib, re, shlex, subprocess, sys, time

base=pathlib.Path(__file__).resolve().parent
root=base.parent.parent
compiler_path=pathlib.Path(sys.argv[1])
compiler=json.loads(compiler_path.read_text())
assert compiler['action']=='compile-main' and compiler['exit_status']==0
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert compiler['source_revision']==revision
for name,digest in compiler['source_sha256'].items():
    assert hashlib.sha256((base/'native'/name).read_bytes()).hexdigest()==digest,name
source=root/'docs/research/v8-full-view-zk-20260912/evidence/r405-generic-batch-translation-frontier/provenance/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc'
input_sha='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
assert hashlib.sha256(source.read_bytes()).hexdigest()==input_sha
host='dombarker@100.108.41.90'
opts=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
runid='aspis-r419-candidate-'+str(time.time_ns())
out=base/'runs'/runid
out.mkdir(parents=True,exist_ok=False)
remote='/home/dombarker/project-offloads/aspis-r419-native-20261002-a/'+runid
binary=compiler['remote_working_directory']+'/normalize'
artifact=json.loads(subprocess.check_output(['ssh',*opts,host,shlex.join(['python3','-c',
    'import pathlib,hashlib,json,sys; p=pathlib.Path(sys.argv[1]); print(json.dumps({"path":str(p),"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"bytes":p.stat().st_size}))',binary])],text=True))
receipt={'target':'fresh native AST R396 candidate copy for complete diff audit',
    'classification':'UNVERIFIED candidate; no Aeneas translation, Lean source execution, or security claim',
    'source_revision':revision,'input_sha256':input_sha,'input_path':str(source),
    'source_sha256':compiler['source_sha256'],'compiler_receipt':str(compiler_path),
    'compiler_receipt_sha256':hashlib.sha256(compiler_path.read_bytes()).hexdigest(),
    'native_binary':artifact,'runner_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
    'resources':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},
    'remote_working_directory':remote,'expected_work':'native deserialize, bounded typed-AST substitution and fresh serialization; no dependency build',
    'print_axioms':'Not applicable: native AST candidate, no Lean theorem.',
    'measurement_boundary':'GNU time native child peak RSS and swaps; systemd scope peak supplementary',
    'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
receipt_path=out/'receipt.json'
receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
subprocess.run(['ssh',*opts,host,'mkdir -p '+shlex.quote(remote)],check=True)
subprocess.run(['scp',*opts,str(source),host+':'+remote+'/original.llbc'],check=True)
script='''import pathlib,hashlib,subprocess,sys,json
facts=json.loads(sys.argv[1]); binary=facts['native_binary']['path']
assert hashlib.sha256(pathlib.Path(binary).read_bytes()).hexdigest()==facts['native_binary']['sha256']
original=pathlib.Path('original.llbc'); output=pathlib.Path('candidate.llbc')
assert hashlib.sha256(original.read_bytes()).hexdigest()==facts['input_sha256']
assert not output.exists()
code=subprocess.call(['/usr/bin/time','-v',binary,str(original),str(output)])
assert hashlib.sha256(original.read_bytes()).hexdigest()==facts['input_sha256']
result={'exit_status':code,'original_post_sha256':hashlib.sha256(original.read_bytes()).hexdigest()}
if output.exists(): result['output_sha256']=hashlib.sha256(output.read_bytes()).hexdigest(); result['output_bytes']=output.stat().st_size
pathlib.Path('result.json').write_text(json.dumps(result,indent=2)+'\\n')
raise SystemExit(code)
'''
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit='+runid,'--working-directory='+remote,
    '-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128',
    'python3','-c',script,json.dumps(receipt)]
receipt['command']=cmd
with (out/'raw.log').open('w') as f:
    status=subprocess.run(['ssh',*opts,host,shlex.join(cmd)],stdout=f,stderr=subprocess.STDOUT)
receipt['exit_status']=status.returncode
raw=(out/'raw.log').read_text()
for key,pat in [('wall_time',r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)'),
                ('peak_rss_kib',r'Maximum resident set size \(kbytes\): (\d+)'),('swaps',r'Swaps: (\d+)')]:
    match=re.search(pat,raw)
    if match: receipt[key]=match[1] if key=='wall_time' else int(match[1])
fetch=subprocess.run(['scp',*opts,host+':'+remote+'/result.json',str(out/'result.json')],capture_output=True,text=True)
receipt['result_fetch_status']=fetch.returncode
if fetch.returncode==0:
    result=json.loads((out/'result.json').read_text())
    receipt['native_result']=result
    if 'output_sha256' in result:
        subprocess.run(['scp',*opts,host+':'+remote+'/candidate.llbc',str(out/'candidate.llbc')],check=True)
        assert hashlib.sha256((out/'candidate.llbc').read_bytes()).hexdigest()==result['output_sha256']
receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
print(raw)
print('RECEIPT',receipt_path)
raise SystemExit(status.returncode)
