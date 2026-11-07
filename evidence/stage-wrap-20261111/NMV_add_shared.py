"""Add only the independent live-shared-loan snapshot boundary class."""
from NMV_program import artifact,E,sha
import difflib,re,subprocess
patch=subprocess.check_output(['git','show','68730c8ae22:evidence/stage-wrap-20261111/NMV_HARNESSES.patch'],text=True)
block=next(b for b in re.split(r'(?=^--- )',patch,flags=re.M) if b.startswith('--- /dev/null\n+++ b/programs/r1-cost-probe/src/NMV_program.rs\n'))
program=''.join(line[1:] for line in block.splitlines(True)[2:] if line.startswith('+'))
assert 'fn NMV_snapshot_readshared()' not in program
program=program.replace('if BRANCH==0 {kani::assume(n==l1||n==l2);}', 'if BRANCH==0 || BRANCH==3 {kani::assume(n==l1||n==l2);}')
program=program.replace('let out=snapshot(&a,', 'let hold_shared=if BRANCH==3 {Some(a.data.borrow())}else{None};\n let out=snapshot(&a,')
program=program.replace('drop(hold);\n assert!(a.try_borrow_mut_data().is_ok());','if BRANCH==3 {assert!(a.try_borrow_mut_data().is_err());}\n drop(hold_shared);drop(hold);\n assert!(a.try_borrow_mut_data().is_ok());')
for name,mode,getter in [('NMV_snapshot_readshared',0,'shared'),('NMV_snapshot_readshared_reply_control',1,'shared'),('NMV_snapshot_readshared_argument_control',2,'shared'),('NMV_snapshot_readshared_footprint_control',3,'shared_omit')]:
 program+='\n#[kani::proof]#[kani::unwind(8)]\n'
 program+=f'#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_data,{getter})]\n'
 program+='#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_mut_data,exclusive)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]\n'
 program+=f'fn {name}(){{snapshot_test::<{mode},3>();}}\n'
blocks=re.split(r'(?=^--- )',patch,flags=re.M)
for i,b in enumerate(blocks):
 if b.startswith('--- /dev/null\n+++ b/programs/r1-cost-probe/src/NMV_program.rs\n'):
  blocks[i]=''.join(difflib.unified_diff([],program.splitlines(True),fromfile='/dev/null',tofile='b/programs/r1-cost-probe/src/NMV_program.rs'))
new=''.join(blocks)
(E/'NMV_HARNESSES.patch').write_text(new)
(E/'NMV_HARNESSES.patch.sha256').write_text(sha(new.encode())+'\n')
