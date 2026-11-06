from pathlib import Path
import difflib,json,hashlib
E=Path(__file__).resolve().parent
code='''
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_shared_from_fn_cut(){
 let values:[QM31;33]=unsafe{core::mem::transmute::<[[u32;4];33],[QM31;33]>(kani::any())};
 let group:usize=kani::any();let seek:usize=kani::any();let limb:usize=kani::any();kani::assume(group>=12&&group<=20&&seek<4&&limb<4);
 let mut calls=0usize;let mut seen=999usize;
 let lanes:[QM31;4]=core::array::from_fn(|slot|{if calls==seek{seen=slot;}calls+=1;let source=4*group+slot;if source>=49&&source<82{values[source-49]}else{QM31::ZERO}});
 let source=4*group+seek;let expected=if source>=49&&source<82{NJL_words(values[source-49])[limb]}else{0};
 assert_eq!(calls,4);assert_eq!(seen,seek);assert_eq!(NJL_words(lanes[seek])[limb],expected ^ if cfg!(NJL_invert){1}else{0});
}
struct NJL_TagForward {calls:usize,coordinate:usize,selectors:usize}
fn NJL_dot_reply(selectors:&Selectors,coordinate:usize,reply:QM31,log:&mut NJL_TagForward)->QM31{log.calls+=1;log.coordinate=coordinate;log.selectors=selectors as *const Selectors as usize;reply}
fn NJL_tag_value(_scratch:&[QM31],coordinate:usize,selectors:&Selectors,reply:QM31,log:&mut NJL_TagForward)->QM31{
 NJL_dot_reply(selectors,coordinate,reply,log)
}
#[kani::proof] #[kani::unwind(67)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_tag_forward_cut(){
 let selectors=Selectors{high:unsafe{core::mem::transmute::<[[u32;4];64],[QM31;64]>(kani::any())},low:unsafe{core::mem::transmute::<[[u32;4];16],[QM31;16]>(kani::any())}};
 let coordinate:usize=kani::any();kani::assume(coordinate<30);let reply=unsafe{core::mem::transmute::<[u32;4],QM31>(kani::any())};
 let mut log=NJL_TagForward{calls:0,coordinate:999,selectors:0};let output=NJL_tag_value(&[],coordinate,&selectors,reply,&mut log);
 let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(log.calls,1);assert_eq!(log.coordinate,coordinate);assert_eq!(log.selectors,&selectors as *const Selectors as usize);
 assert_eq!(NJL_words(output)[limb],NJL_words(reply)[limb] ^ if cfg!(NJL_invert){1}else{0});
}
'''
p=E/'NJL_control.rs.txt';old=p.read_text();new=old+code;p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_SHARED_CONTROL.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins))
p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_shared_from_fn_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_SHARED_CONTROL.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_SHARED_CONTROL.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k,base,name in [(33,25,'NJL_shared_from_fn_cut'),(34,26,'NJL_shared_from_fn_cut'),(35,25,'NJL_tag_forward_cut'),(36,26,'NJL_tag_forward_cut')]:
 x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module=name,command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized small std4callback or deployed tag forwarding native cut; no arithmetic or full-buffer value model')
 x['native_command']=[v.replace('NJL_tag_constructor_cut',name)for v in x['native_command']];x['sources']=list(dict.fromkeys(x['sources']+[p.name for p in E.glob('NJL_*.patch')]));x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
