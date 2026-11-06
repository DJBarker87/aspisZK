from pathlib import Path
import json,difflib,hashlib
E=Path(__file__).resolve().parent;p=E/'NJL_control.rs.txt';old=p.read_text();new=old+'''
fn NJL_words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn NJL_q(w:[u32;4])->QM31{QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
fn NJL_canon(w:[u32;4])->bool{w[0]<2147483647&&w[1]<2147483647&&w[2]<2147483647&&w[3]<2147483647}
struct NJL_AddLog {left:QM31,right:QM31,reply:QM31,calls:usize}
fn NJL_add(a:QM31,b:QM31,log:&mut NJL_AddLog)->QM31 {log.left=a;log.right=b;log.calls+=1;log.reply}
fn NJL_endpoint_write(scratch:&mut[QM31],index:usize,rhs:QM31,log:&mut NJL_AddLog){
 scratch[index]=NJL_add(scratch[index],rhs,log);
}
#[kani::proof] #[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_endpoint_write_cut(){
 let mut scratch:[QM31;103]=unsafe{core::mem::transmute::<[[u32;4];103],[QM31;103]>(kani::any())};
 let index:usize=kani::any();let observe:usize=kani::any();let limb:usize=kani::any();
 kani::assume(index<103&&observe<103&&limb<4);
 let before=NJL_words(scratch[observe]);let old=scratch[index];let rhs:[u32;4]=kani::any();let reply:[u32;4]=kani::any();
 kani::assume(NJL_canon(NJL_words(old))&&NJL_canon(rhs)&&NJL_canon(reply));
 let mut log=NJL_AddLog{left:QM31::ZERO,right:QM31::ZERO,reply:NJL_q(reply),calls:0};
 NJL_endpoint_write(&mut scratch,index,NJL_q(rhs),&mut log);
 assert_eq!(log.calls,1);assert_eq!(NJL_words(log.left)[limb],NJL_words(old)[limb]);assert_eq!(NJL_words(log.right)[limb],rhs[limb]);
 assert_eq!(NJL_words(scratch[observe])[limb],(if observe==index{reply[limb]}else{before[limb]}) ^ if cfg!(NJL_invert){1}else{0});
}
''';p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_ENDPOINT_WINDOW.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));x=json.loads((E/'NJL_SOURCE_PINS.json').read_text());x[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(x));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_endpoint_write_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_ENDPOINT_WINDOW.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_ENDPOINT_WINDOW.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k in [10,11]:
 x=json.loads((E/'NJL_K009.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module='NJL_endpoint_write_cut',command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized ONE scratch write at arbitrary offset and arbitrary observer, two scalar prestates only; NO full103-cell before copy. Missing K072 frame replacement, not same shape')
 x['native_command']=[v.replace('NJL_occupancy_control_cut','NJL_endpoint_write_cut')for v in x['native_command']];x['sources'].append('NJL_ENDPOINT_WINDOW.patch');x['collect']=[v.replace('NJL_K009',a)for v in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJL_invert'if k==11 else'');(E/(a+'.json')).write_text(json.dumps(x))
print('One write/arbitrary observed offset, no whole-array saved prestate; exact native source assignment shape')
