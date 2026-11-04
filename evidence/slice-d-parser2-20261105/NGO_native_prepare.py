from pathlib import Path
import subprocess,json,hashlib,difflib,base64,tarfile,io
E=Path(__file__).resolve().parent; F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
B='/home/dombarker/project-offloads/codex-cx-slice-d-parser2-20261105';H='dombarker@100.108.41.90'
sha=lambda b:hashlib.sha256(b).hexdigest()
archive=subprocess.check_output(['git','archive',F,'crates','programs','Cargo.toml','Cargo.lock'])
files={}
with tarfile.open(fileobj=io.BytesIO(archive)) as t:
 for p in t.getmembers():
  if p.isfile():files[p.name]=t.extractfile(p).read()
frozen={n:sha(b) for n,b in files.items()}
lib='crates/aspis-r1-cost-probe/src/lib.rs';files[lib]+=b'\n#[cfg(kani)] mod NGO_q;\n'
ref=(E/'NGO_references.rs.txt').read_text();ref=ref[ref.index('pub fn NGO_decode_le'):]
s='''use aspis_core::field::{M31,CM31,QM31};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
'''+ref+'''
#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NGO_q_association() {
 let bytes:[u8;16]=kani::any();
 let actual=QM31::from_le_bytes(&bytes);
 let reference=NGO_decode_le(&bytes);
 #[cfg(not(NGO_invert))] assert_eq!(actual,reference);
 #[cfg(NGO_invert)] assert_ne!(actual,reference);
}
'''
files['crates/aspis-r1-cost-probe/src/NGO_q.rs']=s.encode()
inputs={n:b.decode() for n,b in files.items() if n not in frozen or sha(b)!=frozen[n]}
(E/'NGO_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1))
(E/'NGO_FROZEN_SOURCE_PINS.json').write_text(json.dumps(frozen,indent=1))
(E/'NGO_SOURCE_PINS.json').write_text(json.dumps({n:sha(b) for n,b in files.items()},indent=1))
patch=[]
for n,s in inputs.items():
 old=subprocess.check_output(['git','show',F+':'+n]).decode() if n in frozen else ''
 patch+=difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if n in frozen else '/dev/null',tofile='b/'+n)
(E/'NGO_harness.patch').write_text(''.join(patch))
K=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch'
payload=dict(files={n:base64.b64encode(b).decode() for n,b in files.items()},kmx=K.read_text())
code=f'''from pathlib import Path
import subprocess,json,sys,base64
b=Path({B!r});ad=b/'NGO_NATIVE_SETUP-admission.json'
with (b/'NGO_NATIVE_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(ad)],stdout=f,stderr=subprocess.STDOUT)
print(ad.read_text() if ad.exists() else 'MISSING',flush=True)
if not ad.exists() or r.returncode!=0 or json.loads(ad.read_text()).get('allowed') is not True:sys.exit(78)
s=b/'NGO_src';s.mkdir(exist_ok=True)
payload=json.loads({json.dumps(payload)!r})
for n,v in payload['files'].items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
r=subprocess.run(['patch','-p1'],input=payload['kmx'],text=True,cwd=s,capture_output=True);assert r.returncode==0,r.stdout+r.stderr
print(json.dumps(dict(files=len(payload['files']),patch_sha256={sha(K.read_bytes())!r})))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
(E/'NGO_NATIVE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
print(r.stdout)
s=(E.parent/'slice-d-parser-20261104/NGD_gate.py').read_text().replace('NGD_','NGO_')
(E/'NGO_gate.py').write_text(s)
