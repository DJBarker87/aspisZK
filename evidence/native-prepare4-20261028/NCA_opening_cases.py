"""Fix NBR_K030 ownership and split its three native source positions.
Copy bodies are the exact supplied KMX file, never lane-authored replacements.
"""
from pathlib import Path
E=Path(__file__).resolve().parent
s=Path('evidence/native-prepare3-20261028/NBR_K030/sources/NBR_src/crates/aspis-r1-cost-probe/src/NBR_candidate.rs').read_text()
s='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'+s[s.index('#[derive(Clone,Copy)]'):]
for n in ['copy_nonoverlapping','copy_from_slice','clone_from_slice','to_vec','realloc']:s=s.replace('NBR_'+n,'KMX_'+n)
s=s.replace('NBR_','NCA_').replace('if mode==1','else if mode==1').replace('if mode==2','else if mode==2')
for mode in [1,2]:
 t=s.replace('let mode:u8=kani::any();','let mode:u8='+str(mode)+';').replace('fn NCA_opening_positions()','fn NCA_opening_mode'+str(mode)+'()')
 if mode==1:wrong=t.replace('fn NCA_opening_mode1()','fn NCA_opening_mode1_wrong()').replace('assert_eq!(src.as_ptr() as *const u8,NCA_ROOT)','assert_ne!(src.as_ptr() as *const u8,NCA_ROOT)')
 else:wrong=t.replace('fn NCA_opening_mode2()','fn NCA_opening_mode2_wrong()').replace('assert_eq!(g[slot],old[slot])','assert_ne!(g[slot],old[slot])')
 (E/('NCA_opening_mode'+str(mode)+'.rs.txt')).write_text(t);Path('/private/tmp/NCA_opening_mode'+str(mode)+'.rs').write_text(t)
 (E/('NCA_opening_mode'+str(mode)+'_wrong.rs.txt')).write_text(wrong);Path('/private/tmp/NCA_opening_mode'+str(mode)+'_wrong.rs').write_text(wrong)
# Additional destruction-position observation; runtime allocator semantics stay U00.
t=s.replace('let mode:u8=kani::any();','let mode:u8=2;').replace('fn NCA_opening_positions()','fn NCA_opening_drop_position()')
t=t.replace('#[derive(Clone,Copy)]', '''static mut NCA_FREED:bool=false;
unsafe fn NCA_dealloc(ptr:*mut u8,layout:alloc::alloc::Layout){unsafe{if ptr==NCA_PAYLOAD as *mut u8{assert_eq!(layout.size(),256);assert_eq!(layout.align(),1);NCA_FREED=true;}}}
#[derive(Clone,Copy)]''')
t=t.replace('assert_eq!(NCA_MODE,2);assert_eq!(NCA_STAGE,5);','assert_eq!(NCA_MODE,2);assert!(NCA_FREED,"branch Vec drop precedes query");assert_eq!(NCA_STAGE,5);')
t=t.replace('#[kani::proof]','#[kani::stub(alloc::alloc::dealloc,NCA_dealloc)]\n#[kani::proof]')
wrong=t.replace('fn NCA_opening_drop_position()','fn NCA_opening_drop_wrong()').replace('assert!(NCA_FREED,"branch Vec drop precedes query")','assert!(!NCA_FREED,"negative destruction-order control")')
for name,value in [('NCA_opening_drop',t),('NCA_opening_drop_wrong',wrong)]:
 (E/(name+'.rs.txt')).write_text(value);Path('/private/tmp/'+name+'.rs').write_text(value)
