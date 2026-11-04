"""Scratch source inputs; frozen bodies retained, own harnesses only."""
from pathlib import Path
import subprocess,json,hashlib,difflib,base64
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
B='/home/dombarker/project-offloads/codex-cx-slice-d-check-20261104';H='dombarker@100.108.41.90'
C='crates/aspis-r1-cost-probe/src/'
files={};frozen={};binary={}
for n in subprocess.check_output(['git','ls-tree','-r','--name-only',F,'crates','programs'],text=True).splitlines()+['Cargo.lock','Cargo.toml']:
 b=subprocess.check_output(['git','show',F+':'+n]);frozen[n]=hashlib.sha256(b).hexdigest()
 try:files[n]=b.decode()
 except UnicodeDecodeError:binary[n]=base64.b64encode(b).decode()
base=dict(files)
# Only sidecar module declarations and contract annotations are added to bodies.
def annotation(n,sig,attrs):
 assert files[n].count(sig)==1,(n,sig)
 files[n]=files[n].replace(sig,attrs+'\n'+sig,1)
annotation(C+'r1_wire.rs','pub(crate) fn row(&self) -> u8','#[cfg_attr(kani,kani::modifies())]\n    #[cfg_attr(kani,kani::ensures(|r| (*r == self.row) != cfg!(NFU_invert)))]')
files[C+'NFU_wire.rs']='''use super::*;
#[kani::proof_for_contract(ValidatedRecord::row)]
fn row_contract(){let row:u8=kani::any();let r=ValidatedRecord{row,framed:&[]};let _=r.row();}
// Borrowed-return association: same typed slice, no copy, allocation or mutation.
#[kani::proof]
fn framed_identity(){let bytes:[u8;3717]=kani::any();let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=3717&&len<=3717-start);let input=&bytes[start..start+len];let record=ValidatedRecord{row:kani::any(),framed:input};let result=record.framed();assert!((result.as_ptr()==input.as_ptr()&&result.len()==input.len()) != cfg!(NFU_invert));}
#[kani::proof]
fn payload_identity(){let bytes:[u8;3717]=kani::any();let len:usize=kani::any();kani::assume(5<=len&&len<=3717);let r=ValidatedRecord{row:kani::any(),framed:&bytes[..len]};let result=r.payload();assert!((result.as_ptr()==unsafe{bytes.as_ptr().add(5)}&&result.len()==len-5) != cfg!(NFU_invert));}
'''
# Slot-offset loop: actual one step on arbitrary valid prestate. Full function
# controls are a separate Lean induction; instrumentation has exact cfg erasure.
files[C+'NFU_compact.rs']='''use super::*;
#[kani::proof] #[kani::unwind(6)]
fn check_one(){let c:[u8;16]=kani::any();let result=check_values(&c);let valid=(0..4).all(|i|u32::from_le_bytes([c[4*i],c[4*i+1],c[4*i+2],c[4*i+3]])<0x7fffffff);assert!((result==if valid{Ok(())}else{Err(CodecError::NonCanonical)}) != cfg!(NFU_invert));}
'''
# Empty files are still committed inputs, for a stable source manifest.
for name in ['NFU_reference','NFU_transport','NFU_verifier']:files[C+name+'.rs']='// NFU reserved sidecar; no executable harness yet.\n'
for file,module in [('compact.rs','NFU_compact'),('r1_wire.rs','NFU_wire')]:files[C+file]+='\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod '+module+';\n'
inputs={n:s for n,s in files.items() if n not in base or s!=base[n]}
(E/'NFU_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
(E/'NFU_SOURCE_PINS.json').write_text(json.dumps({**frozen,**{n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()}},indent=1)+'\n')
(E/'NFU_FROZEN_SOURCE_PINS.json').write_text(json.dumps(frozen,indent=1)+'\n')
patch=[]
for n,s in inputs.items():patch+=difflib.unified_diff(base.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in base else '/dev/null',tofile='b/'+n)
(E/'NFU_harness.patch').write_text(''.join(patch))
# Host tree is copied once from the retained frozen scratch. All frozen text is
# restored below; KMX files in that tree are verified by the strict run gate.
remote=f'''from pathlib import Path
import json,shutil,base64
b=Path({B!r});s=b/'NFU_src';assert not s.exists()
shutil.copytree('/home/dombarker/project-offloads/codex-cx-slice-d-define-20261104/NFQ_src',s,symlinks=False)
for n,t in json.loads({json.dumps(files)!r}).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
for n,t in json.loads({json.dumps(binary)!r}).items():(s/n).write_bytes(base64.b64decode(t))
(b/'NFU_SOURCE_PINS.json').write_text({(E/'NFU_SOURCE_PINS.json').read_text()!r})
print(json.dumps(dict(files={len(files)},frozen_revision={F!r})))
'''
# Fresh admission is mandatory before uploading source inputs.
a=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=f'''import subprocess,json,sys
from pathlib import Path
b=Path({B!r});p=b/'NFU_NATIVE_SETUP-admission.json'
with (b/'NFU_NATIVE_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/JFz_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''',text=True,capture_output=True)
(E/'NFU_NATIVE_SETUP-admission.log').write_text(a.stdout+a.stderr)
assert a.returncode==0 and json.loads(a.stdout)['allowed'] is True,a.stdout+a.stderr
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=remote,text=True,capture_output=True)
(E/'NFU_NATIVE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
print(r.stdout)
