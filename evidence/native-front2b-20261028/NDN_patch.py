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
 a=s.index('fn interpolate_three_constant_limb(');b=s.index('\n#[inline(always)]',a)
 original=s[a:b];alternate=original
 for i in range(3):
  old='u64::from(weight'+str(i)+') * u64::from(constant'+str(i)+')'
  assert old in alternate
  alternate=alternate.replace(old,'NDN_native::product('+str(i)+',u64::from(weight'+str(i)+'),u64::from(constant'+str(i)+'))')
 gate='all(kani,any(NDN_interpolation_factors,NDN_interpolation_sum))'
 s=s[:a]+'#[cfg(not('+gate+'))]\n'+original+'\n#[cfg('+gate+')]\n'+alternate+s[b:]
 s+='\n#[cfg(kani)]\n#[path="NDN_state_native.rs"] mod NDN_native;\n'
 out={n:s}
 out['crates/aspis-statement/src/NDN_state_native.rs']=(E/'NDN_state_native.rs').read_text()
 n='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
 s=subprocess.check_output(['git','show',REV+':'+n],text=True)
 a=s.index('    fn active_mask_basis(');b=s.index('    fn active(&self)',a)
 body=s[a:b]
 point='        let mut block = 0usize;'
 body=body.replace(point,point+'\n        #[cfg(all(kani,any(NDN_active_high,NDN_active_route,NDN_active_sparse)))] {high_sums=unsafe{NDN_native::PRE};block=unsafe{NDN_native::BLOCK};}',1)
 point='            high_sums[coordinate] = high_sums[coordinate].add(self.high[block]);'
 body=body.replace(point,'            #[cfg(all(kani,NDN_active_route))] {unsafe{NDN_native::COORD=coordinate;NDN_native::LEFT=high_sums[coordinate];NDN_native::RIGHT=self.high[block];}return QM31::ZERO;}\n'+point,1)
 point='            block += 1;'
 body=body.replace(point,point+'\n            #[cfg(all(kani,any(NDN_active_high,NDN_active_route,NDN_active_sparse)))] {unsafe{NDN_native::AFTER=high_sums;NDN_native::NEXT=block;}return QM31::ZERO;}',1)
 body=body.replace('        let mut block = 0usize;','        let mut block = 0usize;\n        #[cfg(all(kani,NDN_active_low))] {block=64;}',1)
 body=body.replace('        let mut coordinate = 0usize;','        let mut coordinate = 0usize;\n        #[cfg(all(kani,NDN_active_low))] {coordinate=unsafe{NDN_native::COORD};}',1)
 point='            sum = sum.add(high_sums[coordinate].mul(low_sum));'
 body=body.replace(point,'            #[cfg(all(kani,NDN_active_low))] {unsafe{NDN_native::LOW_REPLY=low_sum;}return QM31::ZERO;}\n'+point,1)
 s=s[:a]+body+s[b:]
 # Source-window instrumentation: each product receives the arbitrary prior-cut
 # result except the selected multiplication; erasing cfg blocks restores frozen body.
 a=s.index('fn copy_residual(');b=s.index('\n#[inline(always)]',a)
 body=s[a:b]
 # A local trait makes the alternate call spelling explicit, without modifying
 # the frozen core field implementation or creating a Kani method stub.
 body=body.replace('    let denominators = [','    #[cfg(all(kani,NDN_residual_cut))] use NDN_native::CutMul;\n    let denominators = [',1)
 body=body.replace('.mul(','.NDN_mul(')
 # Entire alternate body is cfg-only; real frozen body remains selected otherwise.
 original=s[a:b]
 alternate=body.replace('fn copy_residual(', 'fn copy_residual(',1)
 s=s[:a]+'#[cfg(not(all(kani,NDN_residual_cut)))]\n'+original+'\n#[cfg(all(kani,NDN_residual_cut))]\n'+alternate+s[b:]
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
