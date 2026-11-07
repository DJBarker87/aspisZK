"""Serial PCH scope client; never resubmits a submitted transport failure."""
import pathlib,subprocess,json,sys,time,shlex,hashlib,os,atexit
E=pathlib.Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-pc-reach1-cache-20261110';H='dombarker@100.108.41.90'
a,kind,script=sys.argv[1:]; assert kind in ['build','audit']
guard=E/'PCH_ACTIVE';fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,a.encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
def remote(code,submitted=False):
 for i in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
  with (E/'PCH_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=i,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Recover submitted scope read-only; never resubmit')
  if i<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for i in range(7):
 r=remote(f'import shutil;print(shutil.disk_usage({B!r}).free)'); assert r.returncode==0,r.stderr
 disk=int(r.stdout)
 if disk>=40_000_000_000:break
 if i==6:raise RuntimeError('disk under 40 GB')
 
 for _ in range(10):time.sleep(60)
for i in range(11):
 r=remote(f'''import subprocess,pathlib,sys
b=pathlib.Path({B!r});p=b/{(a+'-barrier-'+str(i)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r};print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr)))
 try:ad=json.loads(r.stdout)
 except ValueError:
  if i==0:time.sleep(30);continue
  raise RuntimeError('infrastructure: missing reservation JSON')
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and i<10:
  print(a+' reservation wait',flush=True)
  for _ in range(3):time.sleep(60)
  continue
 raise RuntimeError('infrastructure admission failure')
files={script:(E/script).read_text()}
for n in ['PCH_BUILD_INPUT.json','PCH_FROZEN.json.xz','PCH_GRAPH_INPUT.json.xz']:
 p=E/n
 if p.exists():files[n]=p.read_bytes().hex()
r=remote(f'''import pathlib,json
b=pathlib.Path({B!r});files=json.loads({json.dumps(files)!r})
for n,v in files.items():
 p=b/n
 if n.endswith(('.xz','.json')):p.write_bytes(bytes.fromhex(v))
 else:p.write_text(v)
''');assert r.returncode==0,r.stderr
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',B+'/'+a+'.time','python3',B+'/'+script,a]
r=remote(f'''import subprocess,pathlib,sys
b=pathlib.Path({B!r})
with (b/{(a+'.stdout')!r}).open('w') as o,(b/{(a+'.stderr')!r}).open('w') as e:r=subprocess.run({cmd!r},stdout=o,stderr=e)
(b/{(a+'.exit')!r}).write_text(str(r.returncode));print('scope {a} exit',r.returncode);sys.exit(r.returncode)
''',submitted=True)
print(r.stdout.strip());(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
# Recover small evidence and explicit compressed compiler outputs only.
r2=remote(f'''import pathlib,json
b=pathlib.Path({B!r}); names=[p.name for p in b.glob({(a+'*')!r}) if p.is_file() and p.stat().st_size<20_000_000];names += [p.name for p in b.glob('PCH_*.json') if p.is_file() and p.stat().st_size<20_000_000 and p.name not in names and p.name!='PCH_BUILD_INPUT.json'];print(json.dumps({{n:(b/n).read_bytes().hex() for n in names}}))
''');assert r2.returncode==0,r2.stderr
for n,v in json.loads(r2.stdout).items():(E/n).write_bytes(bytes.fromhex(v))
rec=dict(attempt=a,scope_kind=kind,exit_status=r.returncode,target=script,command=cmd,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256((E/script).read_bytes()).hexdigest(),disk_free_before_bytes=disk,admission_exit_status=0,admission_allowed=True,print_axioms='N/A: no Lean',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),time_file=a+'.time')
with (E/'PCH_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
sys.exit(r.returncode)
