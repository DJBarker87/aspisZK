import pathlib,subprocess,shlex,json,hashlib,tarfile,io,sys
H=pathlib.Path(__file__).resolve().parent; W=H.parents[2]
HOST='dombarker@100.108.41.90'; OPTS=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
R='/home/dombarker/project-offloads/aspis-r431-actual-slice-construction-20261003-a'
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=W,text=True).strip()
assert rev=='cacf6c885a3beffc89fd6be7e8f3801cd8786d2e'
assert not (H/'launch-status.json').exists() and not (H/'saved-output').exists()
p=H/'remote.py'; sha=hashlib.sha256(p.read_bytes()).hexdigest()
assert sha==sys.argv[1]
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r431-actual-slice-construction','--working-directory=/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','KillMode=control-group','-p','TimeoutStopSec=10s','-p','RuntimeMaxSec=600s','python3','-c',p.read_text()]
probe=subprocess.run(['ssh',*OPTS,HOST,'test ! -e '+shlex.quote(R)])
assert probe.returncode==0,'remote output path exists or access failed; no launch or collection'
argv=['ssh',*OPTS,HOST,shlex.join(cmd)]
(H/'ssh-argv.json').write_text(json.dumps({'argv':argv,'remote_script_sha256':sha,'launch_revision':rev},indent=2))
with (H/'ssh-launch.log').open('wb') as f: proc=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT)
(H/'launch-status.json').write_text(json.dumps({'ssh_exit_status':proc.returncode,'remote_script_sha256':sha,'launch_revision':rev},indent=2))
# Read-only collection, one SSH stream, checked relative files only.
cp=subprocess.run(['ssh',*OPTS,HOST,shlex.join(['tar','-czf','-','-C',R,'.'])],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
(H/'collection.stderr.log').write_bytes(cp.stderr)
(H/'collection-status.json').write_text(json.dumps({'exit_status':cp.returncode,'tar_bytes':len(cp.stdout),'sha256':hashlib.sha256(cp.stdout).hexdigest()},indent=2))
if cp.returncode==0:
 (H/'saved-output').mkdir()
 with tarfile.open(fileobj=io.BytesIO(cp.stdout),mode='r:gz') as t:
  for m in t.getmembers():
   path=pathlib.PurePosixPath(m.name)
   assert not path.is_absolute() and '..' not in path.parts and (m.isfile() or m.isdir()),m.name
  t.extractall(H/'saved-output',filter='data')
print('TERMINAL',proc.returncode,'COLLECTION',cp.returncode)
sys.exit(proc.returncode or cp.returncode)
