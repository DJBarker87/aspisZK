from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent
# Same function/module identifiers and source body as NEF_K002, with Kani nondeterminism fixed to the witnessed value 1.
s='''#![allow(non_snake_case)]
#[derive(Clone,Copy)]
enum Phase {Parsed,Semantic,SemanticPart(u8),Prepare,CheckpointRead,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite,Relation,Final}
type Observer=Option<fn(Phase)>;
mod NBZ_native {
 use super::*;
 static mut NBZ_Q:usize=0;
 static mut NBZ_MARK_CALLS:usize=0;
 fn NBZ_mark_none(obs:Observer,phase:Phase) {
  #[cfg(positive)] assert!(obs.is_none());
  #[cfg(negative)] assert!(obs.is_some());
  match phase {Phase::Query(i)=>unsafe{assert_eq!(i,NBZ_Q);},_=>panic!("wrong phase")}
  unsafe{NBZ_MARK_CALLS+=1;}
 }
 pub fn NBZ_return_carriers() {
  let i:usize=1;
  unsafe{NBZ_Q=i;}
  NBZ_mark_none(None,Phase::Query(i));
  unsafe{assert_eq!(NBZ_MARK_CALLS,1);}
 }
}
fn main() { NBZ_native::NBZ_return_carriers(); }
'''
p=B/'NEF_native_replay.rs';p.write_text(s)
results=[]
for mode in ['positive','negative']:
 binary=B/('NEF_native_replay_'+mode)
 command=['/home/dombarker/.cargo/bin/rustc','--edition=2021','-O','-C','overflow-checks=yes','--cfg',mode,str(p),'-o',str(binary)]
 r=subprocess.run(command,capture_output=True,text=True);assert r.returncode==0,r.stderr
 run=subprocess.run([str(binary)],capture_output=True,text=True)
 results.append(dict(mode=mode,command=command,compile_exit=r.returncode,run_exit=run.returncode,stdout=run.stdout,stderr=run.stderr,binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest()))
assert results[0]['run_exit']==0
assert results[1]['run_exit']!=0 and 'obs.is_some()' in results[1]['stderr']
print(json.dumps(dict(source=s,sha256=hashlib.sha256(s.encode()).hexdigest(),results=results),indent=2))
