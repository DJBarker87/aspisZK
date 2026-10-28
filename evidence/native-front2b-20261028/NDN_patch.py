from pathlib import Path
import difflib,subprocess
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def files():
 n='crates/aspis-statement/src/state_only_poseidon.rs'
 s=(E/'NDN_seed'/n).read_text()
 old='{unsafe{NDE_native::NDE_MATRIX_REPLY=local[NDE_native::NDE_PACKED_ROW][NDE_native::NDE_PACKED_LIMB];}return [0;4];'
 assert old in s
 s=s.replace(old,old+'}',1)
 out={n:s}
 n='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
 s=subprocess.check_output(['git','show',REV+':'+n],text=True)
 a=s.index('    fn active_mask_basis(');b=s.index('    fn active(&self)',a)
 body=s[a:b]
 point='        let mut block = 0usize;'
 body=body.replace(point,point+'\n        #[cfg(all(kani,NDN_active_high))] {high_sums=unsafe{NDN_native::PRE};block=unsafe{NDN_native::BLOCK};}',1)
 point='            block += 1;'
 body=body.replace(point,point+'\n            #[cfg(all(kani,NDN_active_high))] {unsafe{NDN_native::AFTER=high_sums;NDN_native::NEXT=block;}return QM31::ZERO;}',1)
 s=s[:a]+body+s[b:]
 s+='\n#[cfg(kani)]\n#[path="NDN_copy_native.rs"] mod NDN_native;\n'
 out[n]=s
 out['crates/aspis-statement/src/pool_v1/NDN_copy_native.rs']=(E/'NDN_copy_native.rs').read_text()
 out['crates/aspis-statement/src/pool_v1/NDN_reference.rs']=(E/'NDN_reference.rs').read_text()
 patch=''
 for n,s in out.items():
  r=subprocess.run(['git','show',REV+':'+n],capture_output=True,text=True);prior=r.stdout
  patch+=''.join(difflib.unified_diff(prior.splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
 (E/'NDN_harness.patch').write_text(patch)
 return out
