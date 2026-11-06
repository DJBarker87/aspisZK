from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;n='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';p=E/'NIX_src'/n;s=p.read_text()
m='''
#[cfg(kani)] mod NIX_active {
 use super::*;
 fn same(a:QM31,b:QM31)->bool{a.c0.a.0==b.c0.a.0&&a.c0.b.0==b.c0.b.0&&a.c1.a.0==b.c1.a.0&&a.c1.b.0==b.c1.b.0}
 fn canon(a:QM31)->bool{a.c0.a.0<aspis_core::field::P&&a.c0.b.0<aspis_core::field::P&&a.c1.a.0<aspis_core::field::P&&a.c1.b.0<aspis_core::field::P}
 struct Log{a:QM31,b:QM31,count:u8,frame:u64}
 fn add(a:QM31,b:QM31,out:QM31,l:&mut Log)->QM31{l.a=a;l.b=b;l.count+=1;out}
 fn step(high:&[QM31;64],sums:&mut[QM31;7],mut block:usize,out:QM31,l:&mut Log)->(usize,usize){
  let mask=constants::ACTIVE_ROW_MASKS[block];
  let coordinate=match mask{6144=>0,6145=>1,4097=>2,2048=>3,2049=>4,26214=>5,1749=>6,_=>unreachable!("generated Copy active mask outside frozen basis")};
  sums[coordinate]=add(sums[coordinate],high[block],out,l);block+=1;(block,coordinate)
 }
 fn check(negative:bool){
  let high:[QM31;64]=kani::any();let before:[QM31;7]=kani::any();let mut sums=before;let block:usize=kani::any();kani::assume(block<64);let out:QM31=kani::any();kani::assume(canon(out));let count:u8=kani::any();kani::assume(count<255);let frame:u64=kani::any();let mut l=Log{a:kani::any(),b:kani::any(),count,frame};
  let (next,coordinate)=step(&high,&mut sums,block,out,&mut l);if negative{l.frame^=1;}
  const MASKS:[u16;7]=[6144,6145,4097,2048,2049,26214,1749];assert!(coordinate<7);assert_eq!(MASKS[coordinate],constants::ACTIVE_ROW_MASKS[block]);assert_eq!(next,block+1);assert!(same(l.a,before[coordinate])&&same(l.b,high[block]));assert_eq!(l.count,count+1);assert_eq!(l.frame,frame);
  let i:usize=kani::any();kani::assume(i<7);assert!(same(sums[i],if i==coordinate{out}else{before[i]}));
 }
 #[kani::proof] #[kani::unwind(66)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NIX_kmx::KMX_copy_nonoverlapping)] fn native(){check(false);}
 #[kani::proof] #[kani::unwind(66)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NIX_kmx::KMX_copy_nonoverlapping)] fn control(){check(true);}
}
'''
p.write_text(s+m);(E/'NIX_active.rs.txt').write_text(m);pins=json.loads((E/'NIX_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(E/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));x=json.loads((E/'NIX_L070.json').read_text());x.update(attempt='NIX_L072',module='Install active_mask_basis arbitrary-prestate first-loop cell',sources=['NIX_src/'+n,'NIX_SOURCE_PINS.json'],command=['python3','-c','print("Single native first-loop iteration only; initial/grouping/final-loop model association remains separate")']);(E/'NIX_L072.json').write_text(json.dumps(x,indent=2))
for num,kind in [(71,'native'),(72,'control')]:
 a=f'NIX_K{num:03}';x=json.loads((E/'NIX_K058.json').read_text());x.update(attempt=a,module='pool_v1::pair_forest_copy_terminal::NIX_active::'+kind);x['command'][2]=a+'.json';x['native_command'][x['native_command'].index('--harness')+1]=x['module'];x['collect']=[a+z for z in ['-graph-check.json','-graph.stderr','-graph.json','-source-check.json','-lock-check.json']];x['expected_time']='Optimized native single arbitrary first-loop step, opaque addition only; no field products';(E/(a+'.json')).write_text(json.dumps(x,indent=2))
