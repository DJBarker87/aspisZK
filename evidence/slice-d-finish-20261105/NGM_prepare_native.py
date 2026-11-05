from pathlib import Path
import subprocess,json,hashlib,runpy,difflib,base64,time
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';C='crates/aspis-r1-cost-probe/src/'
B='/home/dombarker/project-offloads/codex-cx-slice-d-finish-20261105';H='dombarker@100.108.41.90'
old=runpy.run_path(str(E.parent/'native-front1b-20261028/NDL_sources.py'))['sources']()
def fn(s,name):
 i=s.index('fn '+name+'(');a=s.index('{',i);depth=1;j=a+1
 while depth:
  depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i:j]
ref='\n'.join('pub '+fn(old['NDL_reference.rs'],n) for n in ['qeq_ref','roweq_ref','guard_raw_ref'])+'\n'
harness='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\nmod reference { include!("NGM_reference.rs"); }\n'
harness+='\n'.join(fn(old['NDL_weights.rs'],n) for n in ['qwords','fromq','rawrow'])+'\n'
harness+='pub(super) '+fn(old['NDL_weights.rs'],'guard_raw_post').replace('NDL_bad_guard_raw','NGM_invert')+'\n'
harness+='''#[kani::proof_for_contract(shared_two_point_guard)] #[kani::unwind(12)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''+fn(old['NDL_weights.rs'],'guard_raw_contract')+'\n'
# Exact matching KMX copy fidelity controls, independent of guard's comparison.
harness+='''#[kani::proof] #[kani::unwind(65)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_control(){let src:[u8;64]=kani::any();let mut dst:[u8;64]=kani::any();dst.copy_from_slice(&src);let i:usize=kani::any();kani::assume(i<64);assert!((dst[i]==src[i]) != cfg!(NGM_invert));}
'''
files={};binary={};frozen={}
for n in subprocess.check_output(['git','ls-tree','-r','--name-only',F,'crates','programs'],text=True).splitlines()+['Cargo.lock','Cargo.toml']:
 raw=subprocess.check_output(['git','show',F+':'+n]);frozen[n]=hashlib.sha256(raw).hexdigest()
 try:files[n]=raw.decode()
 except UnicodeDecodeError:binary[n]=base64.b64encode(raw).decode()
base=dict(files)
files[C+'weights.rs']=files[C+'weights.rs'].replace('fn shared_two_point_guard(w:', '#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r| NGM_weights::guard_raw_post(*r,w,folds)))]\nfn shared_two_point_guard(w:')+'\n#[cfg(kani)] #[path="NGM_weights.rs"] mod NGM_weights;\n'
files[C+'lib.rs']='#![cfg_attr(kani,feature(allocator_api))]\n'+files[C+'lib.rs']
files[C+'NGM_reference.rs']=ref;files[C+'NGM_weights.rs']=harness
for n in ['NGM_wire','NGM_compact','NGM_transport','NGM_verifier']:files[C+n+'.rs']='// Prefix-owned reserved sidecar.\n'
inputs={n:s for n,s in files.items() if n not in base or s!=base[n]}
pins={**frozen,**{n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()}}
(E/'NGM_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n');(E/'NGM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(E/'NGM_FROZEN_SOURCE_PINS.json').write_text(json.dumps(frozen,indent=1)+'\n')
patch=[]
for n,s in inputs.items():patch+=difflib.unified_diff(base.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in base else '/dev/null',tofile='b/'+n)
(E/'NGM_harness.patch').write_text(''.join(patch))
(E/'NGM_NATIVE_PROVENANCE.json').write_text(json.dumps(dict(reference='NDL_SOURCE_INPUTS.patch via NDL_sources.py; qeq_ref,roweq_ref,guard_raw_ref; byte-preserved bodies',harness='guard_raw_contract body retained with prefix-owned module; new modifies and exact KMX controls; fresh frozen graph every run',frozen=F,kmx_patch_sha256=hashlib.sha256((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest()),indent=2)+'\n')
code='''from pathlib import Path
import json,subprocess,sys,shutil,base64
b=Path(B)
with (b/'NGM_NATIVE_SETUP-admission.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NGM_NATIVE_SETUP-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NGM_NATIVE_SETUP-admission.json';print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
s=b/'NGM_src'
if not s.exists():shutil.copytree('/home/dombarker/project-offloads/codex-cx-slice-d-define-20261104/NFQ_src',s,symlinks=False,ignore=shutil.ignore_patterns('target','.git'))
for n,t in files.items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
for n,t in binary.items():(s/n).write_bytes(base64.b64decode(t))
(b/'NGM_SOURCE_PINS.json').write_text(json.dumps(pins))
print(json.dumps(dict(files=len(files),frozen=F)))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nF='+repr(F)+'\nfiles='+repr(files)+'\nbinary='+repr(binary)+'\npins='+repr(pins)+'\n'+code,text=True,capture_output=True)
 (E/f'NGM_NATIVE_SETUP-{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout[-1000:],r.stderr[-1500:],flush=True)
 if r.returncode==0:break
 if r.returncode==79 and retry==0:time.sleep(30);continue
 if r.returncode not in [78,255] or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
