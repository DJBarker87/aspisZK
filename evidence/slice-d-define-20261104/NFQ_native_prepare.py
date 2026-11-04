"""Own scratch only. Frozen repository bodies plus cfg(kani)-only annotations."""
from pathlib import Path
import subprocess,hashlib,json,difflib,base64
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
B='/home/dombarker/project-offloads/codex-cx-slice-d-define-20261104';H='dombarker@100.108.41.90'
# Two reference definitions are byte-identical to NCO's extracted source; three
# scalar references are newly extracted as NFQ_Reference.
ref='''// Safe scalar references: no Kani, unsafe, pointers, logs, or mutable statics.
pub fn row_shape_ref(row:u8)->Option<(u8,usize)>{
 match row {
  0|1|3..=13=>Some((0,0)),2=>Some((1,32)),14=>Some((3,32)),
  15..=24=>Some((2,896)),25=>Some((4,3712)),26=>Some((5,928)),_=>None,
 }
}
pub fn compact_row_ref(row:u8)->bool{row>=14}
pub fn folds_ref(v:u8)->usize{if v==0 {1}else{2}}
pub fn final_len_ref(v:u8)->usize{if v==0 {256}else{64}}
pub fn checkpoint_size_ref(v:u8)->usize{if v==0 {4840}else{1768}}
'''
base={};files={};pins={};patch=[];binary={}
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',F,'crates','programs'],cwd=R,text=True).splitlines()+['Cargo.lock','Cargo.toml']
for n in paths:
 data=subprocess.check_output(['git','show',F+':'+n],cwd=R);pins[n]=hashlib.sha256(data).hexdigest()
 try:content=data.decode()
 except UnicodeDecodeError:binary[n]=base64.b64encode(data).decode();continue
 base[n]=content;files[n]=content
C='crates/aspis-r1-cost-probe/src/'
def annotate(file,signature,expr):
 n=C+file;s=files[n];assert s.count(signature)==1
 s=s.replace(signature,'#[cfg_attr(kani, kani::modifies())]\n#[cfg_attr(kani, kani::ensures(|r| (*r == '+expr+') != cfg!(NFQ_invert)))]\n'+signature,1);files[n]=s
annotate('compact.rs','fn compact_row(row: u8)','NFQ_compact::reference::compact_row_ref(row)')
annotate('r1_wire.rs','pub const fn row_shape(row: u8)','NFQ_wire::reference::row_shape_ref(row)')
annotate('transport.rs','pub fn folds(self)','NFQ_transport::reference::folds_ref(NFQ_transport::code(self))')
annotate('transport.rs','pub fn final_len(self)','NFQ_transport::reference::final_len_ref(NFQ_transport::code(self))')
annotate('verifier.rs','pub fn checkpoint_size(v:Variant)','NFQ_verifier::reference::checkpoint_size_ref(NFQ_verifier::code(v))')
for file,mod in [('compact.rs','NFQ_compact'),('r1_wire.rs','NFQ_wire'),('transport.rs','NFQ_transport'),('verifier.rs','NFQ_verifier')]:
 files[C+file]+='\n#[cfg(kani)]\n#[path="'+mod+'.rs"]\nmod '+mod+';\n'
common='use super::*;\n#[path="NFQ_reference.rs"] pub(super) mod reference;\n'
code='pub(super) fn code(v:Variant)->u8{match v {Variant::S1=>0,Variant::S2=>1,Variant::D=>2}}\nfn variant()->Variant{match kani::any::<u8>()%3 {0=>Variant::S1,1=>Variant::S2,_=>Variant::D}}\n'
files[C+'NFQ_reference.rs']=ref
files[C+'NFQ_compact.rs']=common+'#[kani::proof_for_contract(compact_row)]\nfn compact_contract(){let _=compact_row(kani::any());}\n'
files[C+'NFQ_wire.rs']=common+'#[kani::proof_for_contract(row_shape)]\nfn shape_contract(){let _=row_shape(kani::any());}\n'
files[C+'NFQ_transport.rs']=common+code+'#[kani::proof_for_contract(Variant::folds)]\nfn folds_contract(){let _=variant().folds();}\n#[kani::proof_for_contract(Variant::final_len)]\nfn final_len_contract(){let _=variant().final_len();}\n'
files[C+'NFQ_verifier.rs']=common+code+'#[kani::proof_for_contract(checkpoint_size)]\nfn size_contract(){let _=checkpoint_size(variant());}\n'
for n,s in files.items():
 if n in base and s==base[n]:continue
 patch+=difflib.unified_diff(base.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in base else '/dev/null',tofile='b/'+n)
(E/'NFQ_harness.patch').write_text(''.join(patch))
(E/'NFQ_FROZEN_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(E/'NFQ_SOURCE_PINS.json').write_text(json.dumps(({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()} | {n:pins[n] for n in binary}),indent=1)+'\n')
(E/'NFQ_reference.rs.txt').write_text(ref)
# Existing workspace admission was successful; fresh admission below precedes upload.
remote=f'''from pathlib import Path
import subprocess,json,sys,shutil
b=Path({B!r});p=b/'NFQ_NATIVE_SETUP-admission.json'
with (b/'NFQ_NATIVE_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/JFz_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=remote,capture_output=True,text=True)
(E/'NFQ_NATIVE_SETUP-admission.log').write_text(r.stdout+r.stderr);assert r.returncode==0 and json.loads(r.stdout)['allowed'] is True,r.stdout+r.stderr
remote=f'''from pathlib import Path
import json,shutil,base64
b=Path({B!r});s=b/'NFQ_src'
assert not s.exists()
shutil.copytree('/home/dombarker/project-offloads/codex-cx-native-cpilot-20261028/NCO_src',s,symlinks=False)
files=json.loads({json.dumps(files)!r})
for n,text in files.items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
for n,data in json.loads({json.dumps(binary)!r}).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(data))
(b/'NFQ_SOURCE_PINS.json').write_text({(E/'NFQ_SOURCE_PINS.json').read_text()!r})
print(json.dumps(dict(source_files=len(files),frozen_revision={F!r})))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=remote,capture_output=True,text=True)
(E/'NFQ_NATIVE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
print(r.stdout)
