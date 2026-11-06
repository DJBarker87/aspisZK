from pathlib import Path
import json,hashlib,difflib
E=Path(__file__).resolve().parent
code='''
struct NJL_TagControl {seek:usize,seek_reduce:usize,terms:usize,chunks:usize,reductions:usize,index:usize,start:usize,end:usize,rchunk:usize,rlimb:usize}
fn NJL_tag_control(coordinate:usize,log:&mut NJL_TagControl)->([M31;4],usize,usize){
 let output=[M31::ZERO;4];let initial=output;
 let mut index=usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate]);
 let end=usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate+1]);
 while index<end {
  let start=index;let chunk_end=core::cmp::min(index+4,end);let raw=[0u64;4];
  assert_eq!(raw,[0u64;4]);
  while index<chunk_end {
   if log.terms==log.seek {log.index=index;log.start=start;log.end=chunk_end;}
   log.terms+=1;index+=1;
  }
  let mut limb=0usize;
  while limb<output.len(){
   if log.reductions==log.seek_reduce {log.rchunk=log.chunks;log.rlimb=limb;}
   log.reductions+=1;limb+=1;
  }
  log.chunks+=1;
 }
 (initial,index,end)
}
#[kani::proof] #[kani::unwind(274)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_tag_control_cut(){
 let coordinate:usize=kani::any();kani::assume(coordinate<30);
 let first=usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate]);let end=usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate+1]);
 let span=end-first;let chunks=(span+3)/4;let seek:usize=kani::any();let seek_reduce:usize=kani::any();kani::assume(seek<span&&seek_reduce<4*chunks);
 let mut log=NJL_TagControl{seek,seek_reduce,terms:0,chunks:0,reductions:0,index:999,start:999,end:999,rchunk:999,rlimb:999};
 let(initial,index,returned_end)=NJL_tag_control(coordinate,&mut log);
 assert_eq!(returned_end,end);assert_eq!(index,end);assert_eq!(log.terms,span);assert_eq!(log.chunks,chunks);assert_eq!(log.reductions,4*chunks);
 assert_eq!(log.index,first+seek+if cfg!(NJL_invert){1}else{0});
 assert_eq!(log.start,first+4*(seek/4));assert_eq!(log.end,core::cmp::min(first+4*(seek/4)+4,end));
 assert_eq!(log.rchunk,seek_reduce/4);assert_eq!(log.rlimb,seek_reduce%4);
 let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(initial[limb].0,0);
}
#[kani::proof] #[kani::unwind(6)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_tag_constructor_cut(){
 let words:[u32;4]=kani::any();let limb:usize=kani::any();kani::assume(limb<4);
 let out=QM31{c0:CM31::new(M31(words[0]),M31(words[1])),c1:CM31::new(M31(words[2]),M31(words[3]))};
 assert_eq!(NJL_words(out)[limb],words[limb] ^ if cfg!(NJL_invert){1}else{0});
}
'''
p=E/'NJL_control.rs.txt';old=p.read_text();new=old+code;p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_TAG_CONTROL.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_tag_control_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_TAG_CONTROL.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_TAG_CONTROL.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k,base,name in [(23,21,'NJL_tag_control_cut'),(24,22,'NJL_tag_control_cut'),(25,21,'NJL_tag_constructor_cut'),(26,22,'NJL_tag_constructor_cut')]:
 x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module=name,command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized CONTROL only for tag loop/reset or exact native4word constructor; all products remain Lean-discharged, no whole-buffer arithmetic')
 x['native_command']=[v.replace('NJL_tag_registry_cut',name)for v in x['native_command']];x['sources'].append('NJL_TAG_CONTROL.patch');x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
(E/'NJL_TAG_CONTROL.json').write_text(json.dumps(dict(source='copy_tag_coordinate_dot',source_control='first/end from frozen31offsets; chunk_end=min(index+4,end), raw4ZERO; term index++ then limb0..3; output4ZERO; final2CM31 constructors',removed='only data-dependent reads/products/reductions, replaced by LOCAL control recorder',semantics='exact entered term/chunk/reduction positions, both initializers and final constructor; no value credit for erased arithmetic'),indent=2)+'\n')
