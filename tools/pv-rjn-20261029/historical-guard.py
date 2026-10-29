"""Resolve failed-hash history through git, including sparsely excluded receipts."""
from pathlib import Path
import subprocess,json,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjn-20261029';out={}
for rev,prefixes in [('c8fb38ee73',('pv-runjoin',)),('codex/pv-rjq-20261029',('pv-rjq-',))]:
 paths=[p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'evidence'],text=True).splitlines() if len(p.split('/'))==3 and p.split('/')[1].startswith(prefixes) and p.split('/')[-1].startswith('modules-') and p.endswith('.json')]
 proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for path in paths:
  proc.stdin.write((rev+':'+path+'\n').encode());proc.stdin.flush();line=proc.stdout.readline().split();assert len(line)==3,(rev,path,line)
  data=proc.stdout.read(int(line[2]));assert proc.stdout.read(1)==b'\n'
  for v in json.loads(data):
   if not v['accepted']:out[v['source_sha256']]=dict(module=v['module'],source_sha256=v['source_sha256'],receipt_path=path,receipt_revision=rev)
 proc.stdin.close();assert proc.wait()==0
records=sorted(out.values(),key=lambda v:(v['module'],v['source_sha256']));text=json.dumps(records,indent=2)+'\n'
if '--check' in sys.argv:assert (E/'historical-failures.json').read_text()==text
else:(E/'historical-failures.json').write_text(text)
print('Historical guard covers',len(records),'distinct failed source hashes')
