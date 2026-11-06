from pathlib import Path
import json
E=Path(__file__).resolve().parent
s='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn canon(w:[u32;4])->bool{w[0]<2147483647&&w[1]<2147483647&&w[2]<2147483647&&w[3]<2147483647}
#[kani::proof]#[kani::unwind(82)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_tag_lookup(){let selectors:Selectors=unsafe{core::mem::transmute::<[[u32;4];80],Selectors>(kani::any())};let index:usize=kani::any();let limb:usize=kani::any();kani::assume(index<272&&limb<4);let block=usize::from(COPY_TAG_TERMS.0[index]);let value=selectors.high[block];let tag=u64::from(COPY_TAG_TERMS.1[index]);assert!(block<64);assert!(tag<2147483647);assert_eq!(words(value)[limb],words(selectors.high[usize::from(COPY_TAG_TERMS.0[index])])[limb]^if cfg!(NJB_invert){1}else{0});}
struct ProductLog{left:[u64;4],right:[u64;4],reply:[u64;4],calls:usize}
fn NJB_product(a:u64,b:u64,l:&mut ProductLog)->u64{let i=l.calls;assert!(i<4);l.left[i]=a;l.right[i]=b;l.calls+=1;l.reply[i]}
fn NJB_raw_step(mut raw:[u64;4],value:QM31,tag:u64,mut index:usize,l:&mut ProductLog)->([u64;4],usize){
 raw[0]+=NJB_product(u64::from(value.c0.a.0),tag,l);
 raw[1]+=NJB_product(u64::from(value.c0.b.0),tag,l);
 raw[2]+=NJB_product(u64::from(value.c1.a.0),tag,l);
 raw[3]+=NJB_product(u64::from(value.c1.b.0),tag,l);
 index+=1;(raw,index)
}
#[kani::proof]#[kani::unwind(6)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_tag_raw(){let raw:[u64;4]=kani::any();let reply:[u64;4]=kani::any();let value:QM31=unsafe{core::mem::transmute::<[u32;4],QM31>(kani::any())};let tag:u64=kani::any();let index:usize=kani::any();kani::assume(index<272&&tag<2147483647&&canon(words(value)));for j in 0..4{kani::assume(raw[j]<=13835058029512359948&&reply[j]<=4611686009837453316);}let mut l=ProductLog{left:[0;4],right:[0;4],reply,calls:0};let (out,next)=NJB_raw_step(raw,value,tag,index,&mut l);let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(l.calls,4);assert_eq!(l.left[limb],u64::from(words(value)[limb]));assert_eq!(l.right[limb],tag);assert_eq!(next,index+1);assert_eq!(out[limb],raw[limb]+reply[limb]+if cfg!(NJB_invert){1}else{0});}
struct ReduceLog{raw:u64,left:u32,right:u32,reduce_reply:u32,add_reply:u32,reductions:usize,adds:usize}
fn NJB_reduce(raw:u64,l:&mut ReduceLog)->M31{assert_eq!(l.reductions,0);l.raw=raw;l.reductions+=1;M31(l.reduce_reply)}
fn NJB_add(a:M31,b:M31,l:&mut ReduceLog)->M31{assert_eq!(l.adds,0);l.left=a.0;l.right=b.0;l.adds+=1;M31(l.add_reply)}
fn NJB_reduce_step(output:&mut[M31;4],raw:[u64;4],mut limb:usize,l:&mut ReduceLog)->usize{output[limb]=NJB_add(output[limb],NJB_reduce(raw[limb],l),l);limb+=1;limb}
#[kani::proof]#[kani::unwind(6)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_tag_reduce(){let mut output:[M31;4]=unsafe{core::mem::transmute::<[u32;4],[M31;4]>(kani::any())};let before=output;let raw:[u64;4]=kani::any();let limb:usize=kani::any();let k:usize=kani::any();let reduce_reply:u32=kani::any();let add_reply:u32=kani::any();kani::assume(limb<4&&k<4&&output[limb].0<2147483647&&reduce_reply<2147483647&&add_reply<2147483647);let mut l=ReduceLog{raw:0,left:0,right:0,reduce_reply,add_reply,reductions:0,adds:0};let next=NJB_reduce_step(&mut output,raw,limb,&mut l);assert_eq!(l.reductions,1);assert_eq!(l.adds,1);assert_eq!(l.raw,raw[limb]);assert_eq!(l.left,before[limb].0);assert_eq!(l.right,reduce_reply);assert_eq!(next,limb+1);assert_eq!(output[k].0,(if k==limb{add_reply}else{before[k].0})^if cfg!(NJB_invert){1}else{0});}
'''
(E/'NJB_tag.rs.txt').write_text(s)
(E/'NJB_install_tag.py').write_text('''from pathlib import Path
import json,hashlib
b=Path.cwd();s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="NJB_tag.rs"]\\nmod NJB_tag_native;\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();q='crates/aspis-statement/src/pool_v1/NJB_tag.rs';(s/q).write_bytes((b/'NJB_tag.rs.txt').read_bytes());pins[q]=hashlib.sha256((s/q).read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('tag lookup/raw-add/reduce windows installed; multiplication logged only')
''')
x=json.loads((E/'NJB_L070.json').read_text());x.update(attempt='NJB_L082',module='NJB_tag_install',sources=['NJB_install_tag.py','NJB_tag.rs.txt'],command=['python3','NJB_install_tag.py']);(E/'NJB_L082.json').write_text(json.dumps(x))
for i,h in [(66,'NJB_tag_lookup'),(68,'NJB_tag_raw'),(70,'NJB_tag_reduce')]:
 for inv in range(2):
  old='NJB_K063'if inv else'NJB_K062';a=f'NJB_K{i+inv:03}';x=json.loads((E/(old+'.json')).read_text());x['attempt']=a;x['command'][-1]=a+'.json';x['collect']=[p.replace(old,a)for p in x['collect']];x['sources']+=['NJB_tag.rs.txt'];x['native_command'][x['native_command'].index('--harness')+1]='pool_v1::pair_forest_copy_terminal::NJB_tag_native::'+h;x['expected_time']='One arbitrary source read/raw-add/reduce iteration; natural products are opaque logged replies, never multiplication in Kani';(E/(a+'.json')).write_text(json.dumps(x))
