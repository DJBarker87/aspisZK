"""Frozen scratch copy and one-iteration powers windows; no repository Rust edits."""
from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parents[1]
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
B='/home/dombarker/project-offloads/codex-cx-slice-d-prepare-20261104'
files={};pins={}
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',F,'crates','programs'],cwd=R,text=True).splitlines()+['Cargo.lock','Cargo.toml']
for n in paths:
 data=subprocess.check_output(['git','show',F+':'+n],cwd=R);pins[n]=hashlib.sha256(data).hexdigest()
 try:files[n]=data.decode()
 except UnicodeDecodeError:pass
C='crates/aspis-r1-cost-probe/src/'
frozen=files[C+'weights.rs']
files[C+'weights.rs']+='\n#[cfg(kani)]\n#[path="NFW_weights.rs"]\nmod NFW_weights;\n'
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn arbitrary_e()->E {let a:[u32;8]=kani::any();let mut i=0;while i<8 {kani::assume(a[i]<2147483647);i+=1;}E::from_limbs(a).unwrap()}
// The product value stays opaque: this records the exact two operands, then
// returns an unconstrained canonical reply. Lean substitutes wide_mul's law.
struct ProductLog {left:E,right:E,reply:E,calls:usize}
fn product(log:&mut ProductLog,left:E,right:E)->E {log.left=left;log.right=right;log.calls+=1;log.reply}
// Source iteration: only p.mul(x) is replaced by the explicit local-record call.
fn step<const N:usize>(out:&mut [E;N],p:&mut E,i:&mut usize,x:E,log:&mut ProductLog)->bool {
 if *i<N {
  out[*i]=*p;
  *i+=1;
  if *i==N {return true;}
  *p=product(log,*p,x);
  false
 } else {true}
}
fn check<const N:usize>(){
 let mut out=[E::ZERO;N];let mut j=0;while j<N{out[j]=arbitrary_e();j+=1;}
 let row:usize=kani::any();let word:usize=kani::any();kani::assume(row<N&&word<8);
 let before=out[row].to_limbs()[word];let old=arbitrary_e();let x=arbitrary_e();let reply=arbitrary_e();
 let mut p=old;let at:usize=kani::any();kani::assume(at<=N);let mut i=at;
 let mut log=ProductLog{left:E::ZERO,right:E::ZERO,reply,calls:0};
 let done=step(&mut out,&mut p,&mut i,x,&mut log);
 let expected=if at<N&&row==at{old.to_limbs()[word]}else{before};
 assert!((out[row].to_limbs()[word]==expected)!=cfg!(NFW_invert));
 assert_eq!(i,if at<N{at+1}else{at});
 assert_eq!(done,at>=N||at+1==N);
 if at+1<N {assert_eq!(log.calls,1);assert_eq!(log.left.to_limbs()[word],old.to_limbs()[word]);assert_eq!(log.right.to_limbs()[word],x.to_limbs()[word]);assert_eq!(p.to_limbs()[word],reply.to_limbs()[word]);}
 else {assert_eq!(log.calls,0);assert_eq!(p.to_limbs()[word],old.to_limbs()[word]);}
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn powers7_step(){check::<7>();}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn powers29_step(){check::<29>();}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_e(){let src=arbitrary_e();let mut dst=arbitrary_e();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let word:usize=kani::any();kani::assume(word<8);assert!((dst.to_limbs()[word]==src.to_limbs()[word])!=cfg!(NFW_invert));}
'''
files[C+'NFW_weights.rs']=code
patch=''.join(difflib.unified_diff(frozen.splitlines(True),files[C+'weights.rs'].splitlines(True),fromfile='a/'+C+'weights.rs',tofile='b/'+C+'weights.rs'))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+C+'NFW_weights.rs'))
(E/'NFW_powers.patch').write_text(patch);(E/'NFW_weights.rs.txt').write_text(code)
(E/'NFW_FROZEN_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in files.items()})
(E/'NFW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(E/'NFW_NATIVE_INPUTS.json').write_text(json.dumps({n:files[n] for n in [C+'weights.rs',C+'NFW_weights.rs']},indent=1)+'\n')
# Initial copy only; all subsequent uploads use the unchanged capped launcher.
remote=f'''from pathlib import Path
import json,subprocess,shutil,sys
b=Path({B!r});p=b/'NFW_NATIVE_SETUP-admission.json'
with (b/'NFW_NATIVE_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists() or r.returncode!=0 or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
s=b/'NFW_src';assert not s.exists()
shutil.copytree(b.parent/'codex-cx-slice-d-define-20261104/NFQ_src',s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
for n,t in json.loads({json.dumps(files)!r}).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NFW_SOURCE_PINS.json').write_text({(E/'NFW_SOURCE_PINS.json').read_text()!r})
print(json.dumps(dict(files={len(files)},frozen={F!r})))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=remote,text=True,capture_output=True)
(E/'NFW_NATIVE_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
(E/'NFW_gate.py').write_text((E.parent/'slice-d-define-20261104/NFQ_gate.py').read_text().replace('NFQ','NFW'))
print(r.stdout[-500:])
