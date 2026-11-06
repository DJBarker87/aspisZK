from pathlib import Path
import json,hashlib,difflib
E=Path(__file__).resolve().parent
code='''
struct NJL_ArrayWindow { seek:usize, seen:usize, calls:usize, reply:[u32;4] }
fn NJL_lane_oracle(lane:usize, log:&mut NJL_ArrayWindow)->QM31 {
 let reply:[u32;4]=kani::any();
 if log.calls==log.seek {log.seen=lane;log.reply=reply;}
 log.calls+=1;
 QM31{c0:CM31{a:M31(reply[0]),b:M31(reply[1])},c1:CM31{a:M31(reply[2]),b:M31(reply[3])}}
}
fn NJL_absorption_array(log:&mut NJL_ArrayWindow)->[QM31;16] {
 core::array::from_fn(|lane| NJL_lane_oracle(lane,log))
}
#[kani::proof] #[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_absorption_array_cut(){
 let seek:usize=kani::any();kani::assume(seek<16);
 let mut log=NJL_ArrayWindow{seek,seen:99,calls:0,reply:[0;4]};
 let out=NJL_absorption_array(&mut log);
 let limb:usize=kani::any();kani::assume(limb<4);
 let value=[out[seek].c0.a.0,out[seek].c0.b.0,out[seek].c1.a.0,out[seek].c1.b.0];
 assert_eq!(log.calls,16);assert_eq!(log.seen,seek);
 assert_eq!(value[limb],log.reply[limb] ^ if cfg!(NJL_invert){1}else{0});
}
'''
p=E/'NJL_control.rs.txt';old=p.read_text();new=old+code;p.write_text(new)
q='crates/aspis-statement/src/pool_v1/NJL_control.rs';patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+q,tofile='b/'+q));(E/'NJL_ARRAY_WINDOW.patch').write_text(patch)
x=json.loads((E/'NJL_SOURCE_PINS.json').read_text());x[q]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(x))
p=E/'NJL_gate.py';s=p.read_text();needle="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(needle,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_absorption_array_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_ARRAY_WINDOW.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_ARRAY_WINDOW.patch')],cwd=S,check=True)
"""+needle);p.write_text(s)
for k in [5,6]:
 x=json.loads((E/'NJL_K004.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module='NJL_absorption_array_cut',command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized std from_fn one arbitrary output window and fixed control, all16 lane bodies opaque, no arithmetic; compiler then array-window elimination')
 x['native_command']=[v.replace('NJL_active_control_cut','NJL_absorption_array_cut')for v in x['native_command']];x['sources'].append('NJL_ARRAY_WINDOW.patch');x['collect']=[v.replace('NJL_K004',a)for v in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJL_invert'if k==6 else'');(E/(a+'.json')).write_text(json.dumps(x))
print('Prepared one arbitrary 4-byte lane output window under exact from_fn16 constructor')
