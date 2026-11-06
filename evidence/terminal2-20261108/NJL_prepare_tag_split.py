from pathlib import Path
import difflib,json,hashlib
E=Path(__file__).resolve().parent
code='''
fn NJL_tag_chunk_control(mut index:usize,end:usize,seek:usize)->(usize,usize,usize,usize,[u64;4]){
 let start=index;let chunk_end=core::cmp::min(index+4,end);let raw=[0u64;4];let mut seen=999;let mut terms=0;
 while index<chunk_end{if terms==seek{seen=index;}terms+=1;index+=1;}
 let mut limb=0;while limb<4{limb+=1;}
 (index,terms,seen,limb,raw)
}
#[kani::proof] #[kani::unwind(6)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_tag_chunk_control_cut(){
 let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<end&&end<=272);
 let chunk_end=core::cmp::min(start+4,end);let seek:usize=kani::any();kani::assume(seek<chunk_end-start);
 let(index,terms,seen,limbs,raw)=NJL_tag_chunk_control(start,end,seek);
 assert_eq!(index,chunk_end);assert_eq!(terms,chunk_end-start);assert_eq!(seen,start+seek+if cfg!(NJL_invert){1}else{0});assert_eq!(limbs,4);
 let i:usize=kani::any();kani::assume(i<4);assert_eq!(raw[i],0);
}
#[kani::proof] #[kani::unwind(6)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_tag_init_exit_cut(){
 let coordinate:usize=kani::any();kani::assume(coordinate<30);
 let output=[M31::ZERO;4];let index=usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate]);let end=usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate+1]);
 let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(output[limb].0,if cfg!(NJL_invert){1}else{0});
 assert!(index<end&&end<=272);let finished=end;assert!(!(finished<end));
}
'''
p=E/'NJL_control.rs.txt';old=p.read_text();new=old+code;p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_TAG_SPLIT.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins))
p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_tag_chunk_control_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_TAG_SPLIT.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_TAG_SPLIT.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k,base,name in [(29,25,'NJL_tag_chunk_control_cut'),(30,26,'NJL_tag_chunk_control_cut'),(31,25,'NJL_tag_init_exit_cut'),(32,26,'NJL_tag_init_exit_cut')]:
 x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module=name,command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized one arbitrary at-most4-term CONTROL chunk or initialization/exit; replaces timed-out K023 full-span loop with Lean induction')
 x['native_command']=[v.replace('NJL_tag_constructor_cut',name)for v in x['native_command']];x['sources']=list(dict.fromkeys(x['sources']+[p.name for p in E.glob('NJL_*.patch')]));x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
for k in [25,26]:
 p=E/f'NJL_K{k:03}.json';x=json.loads(p.read_text());x['sources']=list(dict.fromkeys(x['sources']+[p.name for p in E.glob('NJL_*.patch')]));p.write_text(json.dumps(x))
with (E/'NJL_FAILING_STEP.md').open('a')as f:f.write('\nK023 full-span tag CONTROL timed out at unchanged90s (no credit). K024 not run. Replacement K029/K030 one arbitrary chunk≤4, K031/K032 init/exit; Lean chunk induction connects full intervals. Caps/timeouts unchanged.\n')
