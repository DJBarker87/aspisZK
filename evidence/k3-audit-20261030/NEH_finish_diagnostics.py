from NEH_host import *
import os
cases={
118:'''use super::*;
static mut NBZ_Q:usize=1;
const NBZ_CONST:Option<core::num::NonZeroUsize>=unsafe{Some(core::num::NonZeroUsize::new_unchecked(1))};
fn NBZ_mark_none(obs:Option<core::num::NonZeroUsize>,phase:Phase){assert!(obs.unwrap().get()==2);let _=phase;}
#[kani::proof] #[kani::unwind(8)] fn NBZ_return_carriers(){unsafe{NBZ_Q=2;} NBZ_mark_none(NBZ_CONST,Phase::Query(1));}
''',
119:'''use super::*;
#[repr(align(8))] struct Aligned([u8;8]);
static mut NBZ_Q:Aligned=Aligned([0;8]);
fn NBZ_mark_none(obs:Option<core::num::NonZeroUsize>,phase:Phase){assert!(obs.is_some());let _=phase;}
#[kani::proof] #[kani::unwind(8)] fn NBZ_return_carriers(){unsafe{NBZ_Q.0[0]=1;} NBZ_mark_none(None,Phase::Query(1));}
''',
120:'''use super::*;
struct Record{q:usize,mark_calls:usize}
fn NBZ_mark_none(obs:Observer,phase:Phase,record:&mut Record){
 assert!(obs.is_some());
 match phase {Phase::Query(i)=>assert_eq!(i,record.q),_=>panic!("wrong phase")}
 record.mark_calls+=1;
}
#[kani::proof] #[kani::unwind(4096)] fn NBZ_return_carriers(){
 let i:usize=kani::any();kani::assume(i==1);
 let mut record=Record{q:i,mark_calls:0};
 NBZ_mark_none(None,Phase::Query(i),&mut record);
 assert_eq!(record.mark_calls,1);
}
'''
}
for n,s in cases.items():
 a=f'NEH_K{n:03}';p=E/(a+'.rs');p.write_text(s)
 with (E/(a+'-driver.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NEH_experiments.py'),a],env={**os.environ,'NEH_SOURCE_FILE':str(p)},stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('own input fault; inspect')
