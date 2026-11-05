"""Strictly admitted capped I/O finalization; no additional proof budget."""
from pathlib import Path
import json,subprocess,shlex,time,sys,lzma,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106';H='dombarker@100.108.41.90';a='NHY_H001'
def ssh(code,data=None,submitted=False):
 for i in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NHY_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=i,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted I/O: recover read-only, never resubmit')
  if i<10:time.sleep(60)
 raise RuntimeError('transport retries exhausted')
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});p=b/{(a+'-reservation.json')!r}
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 ad=json.loads(r.stdout);(E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise RuntimeError('admission rejected; no I/O launch')
x=json.loads((E/'NHY_L080.json').read_text());x.update(attempt=a,kind='inspect',module='NHY_host_finalize',command=['python3','NHY_host_finalize.py'],sources=['NHY_host_finalize.py'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,timeout=180,deps_fingerprint={},expected_time='I/O only: hash/copy own retained Lean objects, verify read-only pins, cleanup own Rust/solver outputs. No compiler/prover/arithmetic gate.')
files={'NHY_host_finalize.py':(E/'NHY_host_finalize.py').read_text(),a+'.json':json.dumps(x)}
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r})
for n,t in json.loads({json.dumps(files)!r}).items():(b/n).write_text(t)
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True);(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names=[str(p.relative_to(b)) for p in (b/{a!r}).rglob('*') if p.is_file()]+[{(a+'.json')!r},'NHY_HOST_FINAL.json','NHY_CACHE_EXPORT.json']
print(json.dumps({{n:(b/n).read_text() for n in names}}))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.suffix=='.log':p.with_suffix(p.suffix+'.xz').write_bytes(lzma.compress(t.encode()));Path(str(p)+'.sha256').write_text(hashlib.sha256(t.encode()).hexdigest()+'  '+p.name+'\n')
 else:p.write_text(t)
receipt=json.loads((E/a/'receipt.json').read_text());assert receipt['exit_status']==0
(E/'NHY_IO_ATTEMPTS.jsonl').write_text(json.dumps(receipt)+'\n');print(json.dumps(dict(status='PASS',kind='I/O only, excluded proof budgets',exit_status=receipt['exit_status'],wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps'])))
