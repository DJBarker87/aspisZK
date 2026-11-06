from pathlib import Path
import json,difflib,hashlib
E=Path(__file__).resolve().parent;p=E/'NJL_control.rs.txt';old=p.read_text();new=old+'''
fn NJL_occupancy_control(log:&mut NJL_Control){
 for lane in 0..aspis_core::poseidon2::DIGEST_ELEMS {log.enter(lane);}
}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_occupancy_control_cut(){
 let seek:usize=kani::any();kani::assume(seek<8);
 let mut log=NJL_Control{seek,seen:999,calls:0};
 NJL_occupancy_control(&mut log);
 assert_eq!(log.calls,8);assert_eq!(log.seen,seek ^ if cfg!(NJL_invert){1}else{0});
}
''';p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_OCC_CONTROL.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));x=json.loads((E/'NJL_SOURCE_PINS.json').read_text());x[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(x))
p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_occupancy_control_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_OCC_CONTROL.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_OCC_CONTROL.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k in [7,8]:
 x=json.loads((E/'NJL_K005.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module='NJL_occupancy_control_cut',command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized fixed8 native iterator CONTROL only, digest body is recording oracle; one control-sequence elimination')
 x['native_command']=[v.replace('NJL_absorption_array_cut','NJL_occupancy_control_cut')for v in x['native_command']];x['sources'].append('NJL_OCC_CONTROL.patch');x['collect']=[v.replace('NJL_K005',a)for v in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJL_invert'if k==8 else'');(E/(a+'.json')).write_text(json.dumps(x))
(E/'NJL_OCC_CONTROL.json').write_text(json.dumps(dict(source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::occupancy_lanes_factored',source_body='for lane in 0..DIGEST_ELEMS {occupancy[3 + lane] = empty.mul(opened[2 + lane]);}',replacement='for lane in 0..aspis_core::poseidon2::DIGEST_ELEMS {log.enter(lane);}',alias='same imported aspis_core::poseidon2::DIGEST_ELEMS',pure_control=True),indent=2))
