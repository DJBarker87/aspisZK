"""Stream verified git blobs to the two explicitly authorized source trees."""
import io,json,subprocess,tarfile,hashlib,sys
from pathlib import Path
O=Path(__file__).parent;x=json.loads((O/(sys.argv[1] if len(sys.argv)>1 else 'EJR_inventory.json')).read_text())
roots={'joint':'aspis-joint-20261019','union':'codex-cx-import-union-20261022'}
# No writes to any surviving cache, candidate, or live worker directory.
p=subprocess.Popen(['ssh','dombarker@100.108.41.90','tar -xf - -C /home/dombarker/project-offloads'],stdin=subprocess.PIPE)
rows=[]
with tarfile.open(fileobj=p.stdin,mode='w|') as t:
 for r in x['selected']:
  z=r['resolution']
  if not z:continue
  b=subprocess.check_output(['git','cat-file','blob',z['blob']]);assert hashlib.sha256(b).hexdigest()==r['sha256']
  path=roots[r['workspace']]+'/sources/'+r['module']+'.lean'
  ti=tarfile.TarInfo(path);ti.size=len(b);ti.mode=0o644;t.addfile(ti,io.BytesIO(b))
  rows.append(dict(workspace=r['workspace'],module=r['module'],source_sha256=r['sha256'],blob=z['blob'],revision=z['revision'],host_path='/home/dombarker/project-offloads/'+path,bytes=len(b)))
p.stdin.close();assert p.wait()==0
(O/(sys.argv[2] if len(sys.argv)>2 else 'EJR_restored-sources.json')).write_text(json.dumps(rows,indent=2)+'\n')
print('restored',len(rows))
