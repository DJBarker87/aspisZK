from pathlib import Path
import subprocess,json,hashlib,lzma,base64
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';P='b936275465600469312d1f058cdc91ea2a11f3dc'
files={};pins={}
for v in json.loads((E.parent/'pc-helpers1-20261110/PCB_FROZEN_INPUTS.json').read_text())['rows']:
 n=v['path'];rev=P if n.startswith('programs/aspis-pool/') else R
 b=subprocess.check_output(['git','show',rev+':'+n]);files[n]=base64.b64encode(b).decode();pins[n]={'revision':rev,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
(E/'PCI_FROZEN_INPUTS.json').write_text(json.dumps(pins,indent=1)+'\n')
payload=base64.b64encode(lzma.compress(json.dumps(files).encode())).decode()
patch=lzma.decompress((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch.xz').read_bytes()) if (E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch.xz').exists() else (E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()
assert hashlib.sha256(patch).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
code='''from pathlib import Path
import subprocess,json,lzma,base64,hashlib,shutil,sys
B=Path('/home/dombarker/project-offloads/codex-pc-deposit-children2-20261110');S=B/'PCI_src'
with (B/'PCI_SOURCE_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3',str(B.parent/'codex-cx-s2h-20261023/S2H_reservation.py'),str(B/'PCI_SOURCE_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=B/'PCI_SOURCE_SETUP-reservation.json';a=json.loads(p.read_text()) if p.exists() else None
if r.returncode!=0 or not a or a.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,admission=a)));sys.exit(r.returncode or 78)
assert shutil.disk_usage(B).free>=40_000_000_000
files=json.loads(lzma.decompress(base64.b64decode(PAYLOAD)))
for n,b in files.items():
 p=S/n;p.parent.mkdir(parents=True,exist_ok=True);data=base64.b64decode(b)
 if p.exists():assert p.read_bytes()==data,n
 else:p.write_bytes(data)
patch=base64.b64decode(PATCH);(B/'PCI_KMX.patch').write_bytes(patch)
r=subprocess.run(['git','apply','--check',str(B/'PCI_KMX.patch')],cwd=S,capture_output=True,text=True);assert r.returncode==0,r.stderr
r=subprocess.run(['git','apply',str(B/'PCI_KMX.patch')],cwd=S,capture_output=True,text=True);assert r.returncode==0,r.stderr
pins={str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for p in S.rglob('*') if p.is_file()};(B/'PCI_SOURCE_PINS.json').write_text(json.dumps(pins))
print(json.dumps(dict(files=len(pins),lock=pins['Cargo.lock'],kmx_patch=hashlib.sha256(patch).hexdigest(),admission=a,disk_free=shutil.disk_usage(B).free)))
'''.replace('PAYLOAD',repr(payload)).replace('PATCH',repr(base64.b64encode(patch).decode()))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
(E/'PCI_SOURCE_SETUP.log').write_text(r.stdout+r.stderr);print('PCI source setup exit',r.returncode,r.stdout[-700:],r.stderr[-500:]);raise SystemExit(r.returncode)
