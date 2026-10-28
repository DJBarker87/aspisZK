from pathlib import Path
import sys,json,lzma,base64,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCL_host as h
attempts=[f'NCL_L{i:03}' for i in range(40,50)]
code=f'''from pathlib import Path
import json,lzma,base64,hashlib,subprocess,re
b=Path({h.B!r});out={{}};status=[]
for a in {attempts!r}:
 names=[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-launcher.log',a+'-reservation.json',a+'.json']
 names += [str(p.relative_to(b)) for p in b.glob(a+'-barrier-*.log')]
 for n in names:
  if (b/n).is_file():out[n]=(b/n).read_text()
 status.append(dict(attempt=a,receipt=(b/a/'receipt.json').is_file(),attempt_directory=(b/a).is_dir(),barriers=[str(p.name) for p in b.glob(a+'-barrier-*.log')]))
rows=subprocess.check_output(['ps','-eo','args='],text=True).splitlines()
live=[x for x in rows if re.match(r'^(?:/usr/bin/)?python3 S2W_(?:run|lean)_host[.]py NCL_',x.strip()) or re.match(r'^(?:timeout \d+ )?\S*/(?:lake|lean)\s.*NCL_generated/NCL_R_',x.strip())]
raw=json.dumps(out).encode();print(json.dumps(dict(data=base64.b64encode(lzma.compress(raw,preset=6)).decode(),sha256=hashlib.sha256(raw).hexdigest(),status=status,observed_live_own_launchers=live)))
'''
r=h.remote_py(code);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);raw=lzma.decompress(base64.b64decode(out.pop('data')));assert hashlib.sha256(raw).hexdigest()==out['sha256']
for n,s in json.loads(raw).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
ledger={json.loads(s)['attempt'] for s in (E/'NCL_ATTEMPTS.jsonl').read_text().splitlines()}
for st in out['status']:
 a=st['attempt']
 if st['receipt'] and a not in ledger:
  rc=json.loads((E/a/'receipt.json').read_text())
  with (E/'NCL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
(E/'NCL_BATCH_RECOVERY.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
