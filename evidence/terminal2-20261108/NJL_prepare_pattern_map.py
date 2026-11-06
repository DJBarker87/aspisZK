from pathlib import Path
import difflib,json,hashlib
E=Path(__file__).resolve().parent
code='''
#[kani::proof] #[kani::unwind(75)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_pattern_actual_map_cut(){
 use aspis_core::field::NJB_observe::{prepared_words,prepared_from_words};
 let powers:[QM31;8]=unsafe{core::mem::transmute::<[[u32;4];8],[QM31;8]>(kani::any())};let before=powers;
 let caches:[[[[u32;3];3];8];1]=kani::any();let seek:usize=kani::any();let limb:usize=kani::any();let row:usize=kani::any();let col:usize=kani::any();kani::assume(seek<8&&limb<4&&row<3&&col<3);
 let mut calls=0usize;let mut seen=QM31::ZERO;let mut index=999usize;
 let prepared:[PreparedQm31Multiplier;8]=powers.map(|power|{let i=calls;if i==seek{seen=power;index=i;}calls+=1;prepared_from_words(caches[0][i])});
 assert_eq!(calls,8);assert_eq!(index,seek);assert_eq!(NJL_words(seen)[limb],NJL_words(before[seek])[limb]);assert_eq!(prepared_words(prepared[seek])[row][col],caches[0][seek][row][col]^if cfg!(NJL_invert){1}else{0});
}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_pattern_power_control_cut(){
 let lambda=unsafe{core::mem::transmute::<[u32;4],QM31>(kani::any())};let mut powers=[QM31::ZERO;8];let mut power=lambda;let mut slot=0usize;let seek:usize=kani::any();kani::assume(seek<8);let mut seen=999;let mut calls=0;
 while slot<powers.len(){powers[slot]=power;if slot==seek{seen=slot;}calls+=1;power=lambda;slot+=1;}
 assert_eq!(slot,8);assert_eq!(calls,8);assert_eq!(seen,seek+if cfg!(NJL_invert){1}else{0});
}
'''
p=E/'NJL_control.rs.txt';old=p.read_text();new=old+code;p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_PATTERN_MAP.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_pattern_actual_map_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATTERN_MAP.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATTERN_MAP.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k,base,name in[(45,43,'NJL_pattern_actual_map_cut'),(46,44,'NJL_pattern_actual_map_cut'),(47,43,'NJL_pattern_power_control_cut'),(48,44,'NJL_pattern_power_control_cut')]:
 x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module=name,command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized actual std8map/9word cached output window or data-independent8power loop control only; no field arithmetic')
 x['native_command']=[v.replace('NJL_path_parent_cut',name)for v in x['native_command']];x['sources']=list(dict.fromkeys(x['sources']+[p.name for p in E.glob('NJL_*.patch')]));x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
