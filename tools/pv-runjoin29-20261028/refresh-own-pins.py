"""Refresh h5 HEAD pins only when the already-resolved import closure is unchanged."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin29-20261028'
p=E/'focused-resolution.json';r=json.loads(p.read_text());old=hashlib.sha256(p.read_bytes()).hexdigest()
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
batch=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
updates=[]
for m,x in r['resolved'].items():
 if x.get('authority')!='h5 own git-tracked HEAD':continue
 batch.stdin.write((head+':'+x['path']+'\n').encode());batch.stdin.flush()
 header=batch.stdout.readline().decode().split();assert len(header)==3,(m,header)
 b=batch.stdout.read(int(header[2]));assert batch.stdout.read(1)==b'\n'
 sha=hashlib.sha256(b).hexdigest()
 if sha!=x['sha256']:
  imports=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
  assert imports==x['imports'],(m,'imports changed: run full resolver')
  updates.append(dict(module=m,old_sha256=x['sha256'],new_sha256=sha,old_blob=x['git_blob'],new_blob=header[0]))
 x.update(git_blob=header[0],sha256=sha,git_revision=head)
batch.stdin.close();batch.wait();r['head']=head;p.write_text(json.dumps(r,indent=2)+'\n')
(E/'own-pin-refresh.json').write_text(json.dumps(dict(previous_resolution_sha256=old,head=head,updates=updates,all_h5_sources_read_at_HEAD=True,import_closure_unchanged=True),indent=2)+'\n')
print('Refreshed h5 source pins at',head,'body-only changes',updates)
