#!/usr/bin/env python3
"""Exact candidate-2 marker source and observer-use inventory; no closure claim."""
from pathlib import Path
import subprocess,json,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4]
candidate='190e1779c3b9530047e4d2dfcdf0022b200d6c35';parent='0330ae7300b3df6602600a727dfd1b969bfbe19a';production='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(rev,path):return subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
def item(src,anchor):
 start=src.index(anchor);j=src.index(b'{',start);k=j+1;depth=1
 while depth:depth+=(src[k:k+1]==b'{')-(src[k:k+1]==b'}');k+=1
 return start,k,src[start:k]
pins=[];out={};vp='crates/aspis-r1-cost-probe/src/verifier.rs'
src=read(candidate,vp);assert src==read(parent,vp)
fragments=[]
for name,anchor in [('phase',b'pub enum Phase '),('mark',b'fn mark(obs:Observer,p:Phase)')]:
 start,end,raw=item(src,anchor);pins.append(dict(name=name,path=vp,revision=candidate,start_byte=start,end_byte_exclusive=end,file_sha256=sha(src),fragment_sha256=sha(raw)))
 out['fragments/'+name+'.rs']=raw
 fragments.append(raw)
lib=fragments[0]+b'\npub type Observer=Option<fn(Phase)>;\n'+fragments[1].replace(b'fn mark(',b'pub fn mark(',1)+b'\n'
out['lib.rs']=lib
out['Cargo.toml']=b'[package]\nname="aspis-r1-profiling"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n'
out['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-profiling"\nversion = "0.0.0"\n'
inventory=[]
for rev in [parent,candidate,production]:
 for path in [vp,'crates/aspis-r1-cost-probe/src/r1_semantic.rs','programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs']:
  raw=read(rev,path)
  inventory.append(dict(revision=rev,path=path,sha256=sha(raw),observer_lines=[dict(line=i,text=line) for i,line in enumerate(raw.decode().splitlines(),1) if 'obs' in line or 'mark(' in line or 'cu-profiling' in line]))
metadata=dict(candidate=candidate,parent=parent,production=production,pins=pins,source_inventory=inventory,kit_files={n:sha(b) for n,b in out.items()},scope='Exact source marker only. Full observer-sensitive call closure and fixed Solana callback effect/resource binding remain separate obligations. No source equivalence is inferred from inventory alone.')
out['source-pins.json']=(json.dumps(metadata,indent=2)+'\n').encode()
for name,raw in out.items():
 p=tool/'profiling-marker-input'/name
 if args.check:assert p.read_bytes()==raw,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
print(json.dumps(dict(check=args.check,files=len(out),lib_sha256=sha(lib))))
