from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent
S='c535295ce34bc21ad5670da20bf61c8815e219de';T='83e7049f775afb6fb6a1044d5298b5de3d589f12';R='100d9075d2fcd8adbde84cd548a0e42e55df93ce'
def get(rev,p):return subprocess.check_output(['git','show',rev+':'+p])
def save(rev,p,name):
 b=get(rev,p);q=E/'original'/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);return json.loads(b) if name.endswith('.json') else b
pins=save(S,'evidence/pv-k3scan-20261101/D549-TOOL-PINS.json','tools.json')
for n in ['K79200','K79201','K79220','K79221','K79222','K79223']:
 for f in ['receipt.json','source-sha256.json']:
  save(S,'evidence/pv-k3scan-20261101/host/'+n+'/'+f,n+'/'+f)
for n in ['K12','K13']:
 for f in ['receipt.json','source-manifest.json']:
  save(R,'evidence/pv-kstub-20261028/'+n+'/'+f,n+'/'+f)
for n in ['K93109','K93110','K93111']:
 for f in ['receipt.json','command.json','output.log']:
  save(T,'evidence/pv-stx-20261104/'+n+'/'+f,n+'/'+f)
# Exact original project tree manifest for the stx source cohort; no same-name substitution.
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',T,'tools/pv-stx-20261104/clone-certificate','crates/aspis-core']).decode().splitlines()
manifest={p:hashlib.sha256(get(T,p)).hexdigest() for p in paths}
(E/'original/stx-source-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
for p in ['K3-ROWS.md','REPORT-D549.md','K3-CREDITS.md']:
 save(S,'evidence/pv-k3scan-20261101/'+p,p)
print('prepared',len(manifest),'stx pins')
