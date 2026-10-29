from pathlib import Path
from NEC_templates import template
import subprocess,os,difflib
E=Path(__file__).resolve().parent;R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def files():
 def frozen(n):return subprocess.check_output(['git','show',R+':'+n],text=True)
 from NEC_arbitrary import additions
 out=additions()
 n='crates/aspis-statement/src/lib.rs'
 out[n]='#![cfg_attr(kani, feature(allocator_api))]\n'+frozen(n)+'\n#[cfg(kani)] mod NEC_kmx { extern crate alloc; include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n'
 out['crates/aspis-statement/src/pool_v1/NEC_decode.rs']=template('NEC_decode').replace('if kani::any(){let x:',('if false{let x:' if os.environ.get('NEC_BRANCH')=='error' else 'if true{let x:' if os.environ.get('NEC_BRANCH')=='success' else 'if kani::any(){let x:')).replace('NEC_OBLIGATION',os.environ.get('NEC_OBLIGATION','same && calls')).replace('NEC_GROUP',os.environ.get('NEC_GROUP','0')).replace('NEC_NEGATIVE','true' if os.environ.get('NEC_INVERT') else 'false')
 out['crates/aspis-statement/src/pool_v1/NEC_reference.rs']=template('NEC_reference')
 n='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'
 s=frozen(n)
 for name,post,length in [('decode_pair_afterstate_boxed_v1','post_after',688),('decode_pair_live_snapshot_boxed_v1','post_live',800)]:
  attrs='#[cfg_attr(kani,kani::requires(bytes.len()=='+str(length)+'))]\n#[cfg_attr(kani,kani::ensures(|r| NEC_decode::'+post+'(r,bytes)))]\n'
  attrs+='#[cfg_attr(kani,kani::modifies(&raw mut NEC_decode::CALLS,&raw mut NEC_decode::PTR,&raw mut NEC_decode::LEN,&raw mut NEC_decode::WORD,&raw mut NEC_decode::AFTER_ERROR,&raw mut NEC_decode::LIVE_ERROR))]\n'
  s=s.replace('fn '+name+'(',attrs+'fn '+name+'(',1)
 out[n]=s+'\n#[cfg(kani)] #[path="NEC_decode.rs"] mod NEC_decode;\n'
 patch=[]
 for n,s in out.items():
  r=subprocess.run(['git','show',R+':'+n],capture_output=True,text=True);b=r.stdout if r.returncode==0 else ''
  patch.append(''.join(difflib.unified_diff(b.splitlines(True),s.splitlines(True),fromfile='a/'+n if b else '/dev/null',tofile='b/'+n)))
 (E/'NEC_native.patch').write_text(''.join(patch));return out
