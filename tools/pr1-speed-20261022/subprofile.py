from pathlib import Path
import re,sys
r=Path(sys.argv[1])
prof='''
extern crate std;
mod subprof {
 use std::{collections::BTreeMap,sync::Mutex,time::Instant};
 static TIMES: Mutex<BTreeMap<&'static str,(u64,f64)>>=Mutex::new(BTreeMap::new());
 pub struct Timer(pub &'static str,pub Instant);
 impl Drop for Timer {fn drop(&mut self){let t=self.1.elapsed().as_secs_f64();let mut m=TIMES.lock().unwrap();let e=m.entry(self.0).or_default();e.0+=1;e.1+=t;}}
 pub fn dump(){for (k,(n,t)) in TIMES.lock().unwrap().iter(){std::eprintln!("SUBPROFILE {k} {n} {t}");}}
}
'''
files={
'docs/research/v8-r0-zk-20261009/c3/check/src/lib.rs':['ents_ok','prod_ok','check'],
'docs/research/v8-r0-zk-20261009/c3/build/src/lib.rs':['fill_tq','fill_lo','fill_own','fill_rel','fill_round','fill_gbat'],
'docs/research/v8-r0-zk-20261009/z4/z9c.rs':['insert','express','invert','emit'],
'docs/research/v8-r0-zk-20261009/z4/z9d.rs':['family','image','matmul','convert'],
'docs/research/v8-r0-zk-20261009/z4/z9e.rs':['extracted_builders']}
for name,funcs in files.items():
 p=r/name;s=p.read_text();s+='\n'+prof
 for f in funcs:
  pat=r'((?:pub )?fn '+f+r'\([^\{]+\{)'
  s,n=re.subn(pat,lambda m:m[0]+'\n let _subtimer = subprof::Timer("'+name.split('/')[-3]+'/'+f+'", std::time::Instant::now());',s,count=1);assert n,f
 if name.endswith('z9e.rs'):
  s=s.replace('    (matches!(verdict, Ok(Some(true))), tm)','    aspis_r1_cert_build::subprof_dump(); aspis_r1_cert_check::subprof_dump(); super::super::subprof::dump(); super::subprof::dump(); subprof::dump();\n    (matches!(verdict, Ok(Some(true))), tm)')
 if '/c3/' in name:s+='\npub fn subprof_dump(){subprof::dump();}\n'
 p.write_text(s)
