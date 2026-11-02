from pathlib import Path
import subprocess,json,hashlib,lzma,base64
E=Path(__file__).resolve().parent
remote='''from pathlib import Path
import json,hashlib,base64
r=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028');out={'runs':{},'files':{},'missing':[]}
for ident in ['K26','K28']:
 d=json.loads((r/ident/'source-manifest.json').read_text());out['runs'][ident]={'manifest':d,'manifest_sha256':hashlib.sha256((r/ident/'source-manifest.json').read_bytes()).hexdigest()}
 for x in d:
  p=r/x['path'];candidates=[r/ident/'sealed.rs.txt'] if x['path']=='split/src/sealed.rs' else [r/ident/'KMX_stubs.rs.txt'] if x['path']=='KMX_stubs.rs' else []
  candidates.append(p);found=False
  for q in candidates:
   if not q.exists() or not q.is_file():continue
   b=q.read_bytes()
   if hashlib.sha256(b).hexdigest()==x['sha256']:
    out['files'][x['sha256']]={'path':str(q),'original_path':x['path'],'base64':base64.b64encode(b).decode()};found=True;break
  if not found:out['missing'].append({'run':ident,**x})
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=remote,capture_output=True,text=True);assert r.returncode==0,r.stderr;d=json.loads(r.stdout);raw=json.dumps(d,indent=2).encode();(E/'SPLIT-IMMUTABLE-RECOVERY.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'SPLIT-IMMUTABLE-RECOVERY.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
for h,x in d['files'].items():
 if x['original_path'].endswith('.rs'):
  b=base64.b64decode(x['base64']);assert hashlib.sha256(b).hexdigest()==h;(E/'blobs'/(h+'.rs')).write_bytes(b)
print('Recovered',len(d['files']),'exact snapshot hashes; unresolved',len(d['missing']))
