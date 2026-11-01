"""Finite diagnostic matrix; no successful diagnostic is proof credit."""
from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
base='''use super::*;
{decl}
fn NBZ_mark_none(obs:Option<core::num::NonZeroUsize>,phase:Phase){{assert!(obs.is_some());let _=phase;}}
#[kani::proof] #[kani::unwind(8)]
fn NBZ_return_carriers(){{{write} NBZ_mark_none(None,Phase::Query(1));}}
'''
cases=[
('020','static NBZ_Q:core::sync::atomic::AtomicUsize=core::sync::atomic::AtomicUsize::new(0);','NBZ_Q.store(1,core::sync::atomic::Ordering::SeqCst);'),
('021','struct Wrap(core::cell::UnsafeCell<usize>);unsafe impl Sync for Wrap {} static NBZ_Q:Wrap=Wrap(core::cell::UnsafeCell::new(0));','unsafe{*NBZ_Q.0.get()=1;}'),
('022','static mut NBZ_Q:usize=0; static NBZ_UNWRITTEN:Option<core::num::NonZeroUsize>=None;','unsafe{NBZ_Q=1;} assert!(NBZ_UNWRITTEN.is_some());'),
('023','static mut NBZ_Q:usize=1;','unsafe{NBZ_Q=2;}'),
('024','static mut NBZ_Q:[u8;8]=[0;8];','unsafe{NBZ_Q[0]=1;}'),
('025','static mut NBZ_Q:u32=0;','unsafe{NBZ_Q=1;}'),
('026','static mut NBZ_Q:u64=0;','unsafe{NBZ_Q=1;}'),
('027','static mut NBZ_Q:Option<core::num::NonZeroUsize>=None;','unsafe{NBZ_Q=core::num::NonZeroUsize::new(1);}'),
('028','static mut NBZ_Q:[usize;1]=[0];','unsafe{NBZ_Q[0]=1;}'),
('029','static mut NBZ_Q:usize=0;','let _x=unsafe{NBZ_Q};'),
]
for n,decl,write in cases:
 a='NEH_K'+n;p=E/(a+'.rs');p.write_text(base.format(decl=decl,write=write))
 with (E/(a+'-driver.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NEH_experiments.py'),a],env={**os.environ,'NEH_SOURCE_FILE':str(p)},stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('driver fault')
