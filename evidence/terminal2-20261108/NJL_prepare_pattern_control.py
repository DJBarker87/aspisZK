from pathlib import Path
import json,difflib,hashlib
E=Path(__file__).resolve().parent;p=E/'NJL_control.rs.txt';old=p.read_text();new=old+'''
struct NJL_PatternControl {seek:usize,calls:usize,group:usize,coordinate:usize}
fn NJL_pattern_control(log:&mut NJL_PatternControl)->usize {
 let mut group=0usize;
 while group<4 {
  let mut coordinate=COPY_PATTERN_GROUP_OFFSETS[group];
  while coordinate<COPY_PATTERN_GROUP_OFFSETS[group+1] {
   if log.calls==log.seek {log.group=group;log.coordinate=coordinate;}
   log.calls+=1;coordinate+=1;
  }
  group+=1;
 }
 group
}
#[kani::proof] #[kani::unwind(28)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_pattern_control_cut(){
 let seek:usize=kani::any();kani::assume(seek<26);
 let mut log=NJL_PatternControl{seek,calls:0,group:999,coordinate:999};
 let next=NJL_pattern_control(&mut log);
 let expected_group=if seek<9{0}else if seek<12{1}else if seek<21{2}else{3};
 assert_eq!(next,4);assert_eq!(log.calls,26);assert_eq!(log.group,expected_group);
 assert_eq!(log.coordinate,seek ^ if cfg!(NJL_invert){1}else{0});
}
''';p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_PATTERN_CONTROL.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_pattern_control_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATTERN_CONTROL.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATTERN_CONTROL.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k,base in [(17,15),(18,16)]:
 x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module='NJL_pattern_control_cut',command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized exact frozen2-level while CONTROL only, source field bodies replaced by local recorder; no arithmetic, one scalar selected control position')
 x['native_command']=[v.replace('NJL_endpoint_write_cut','NJL_pattern_control_cut')for v in x['native_command']];x['sources'].append('NJL_PATTERN_CONTROL.patch');x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
(E/'NJL_PATTERN_CONTROL.json').write_text(json.dumps(dict(source='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_pattern_basis_values',source_guard='group<values.len() [len4]; coordinate<COPY_PATTERN_GROUP_OFFSETS[group+1]',replacement='ONLY arithmetic body -> local record, both counters/increments kept',positions=26,group_offsets=[0,9,12,21,26],source_order='groups0..3, coordinates0..25 in increasing order',new_native='control only; values from NJB_K036/037 and038/039'),indent=2))
