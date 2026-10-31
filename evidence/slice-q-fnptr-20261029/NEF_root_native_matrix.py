from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent
# These inputs are uploaded by NEF_root_native_upload.py, not read from another worker.
records=[]
for label in ['nonzero','reference','array','scalar']:
 p=B/('NEF_root_'+label+'.rs.txt');s=p.read_text()
 s=s.replace('#[kani::proof]','').replace('#[kani::unwind(4096)]','').replace('let i:usize=kani::any();kani::assume(i==1);','let i:usize=1;').replace('fn NBZ_return_carriers()', 'pub fn NBZ_return_carriers()')
 s='''#![allow(non_snake_case,dead_code)]
#[derive(Clone,Copy)]
enum Phase { Parsed,Semantic,SemanticPart(u8),Prepare,CheckpointRead,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite,Relation,Final }
type Observer=Option<fn(Phase)>;
mod NBZ_native {
'''+s+'\n}\nfn main(){NBZ_native::NBZ_return_carriers();}\n'
 path=B/('NEF_root_'+label+'.rs');path.write_text(s);binary=B/('NEF_root_'+label)
 command=['/home/dombarker/.cargo/bin/rustc','-O','-C','overflow-checks=yes','--edition=2021',str(path),'-o',str(binary)]
 r=subprocess.run(command,capture_output=True,text=True);assert r.returncode==0,r.stderr
 r=subprocess.run([str(binary)],capture_output=True,text=True);assert r.returncode==101,(label,r.returncode)
 records.append(dict(shape=label,source_sha256=hashlib.sha256(s.encode()).hexdigest(),compile_command=command,compile_exit=0,native_exit=r.returncode,stderr=r.stderr))
print(json.dumps(records,indent=2))
