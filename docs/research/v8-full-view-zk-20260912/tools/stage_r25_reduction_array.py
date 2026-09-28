#!/usr/bin/env python3
"""Remove nested by-value array mapping from the fixed nine-channel reduction."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==180 and 'r25_reconstruction_width'in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists() and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
field=dst/'crates/aspis-core/src/field.rs';s=field.read_text()
old='''    let r=sums.map(|row|row.map(|x|u64::from(M31::reduce_u64(x).0)));
    let [a,b,c,d,e,f,g,h,i]=[r[0][0],r[0][1],r[0][2],r[1][0],r[1][1],r[1][2],r[2][0],r[2][1],r[2][2]];'''
new='\n'.join(f'    let {name}=u64::from(M31::reduce_u64(sums[{i//3}][{i%3}]).0);'for i,name in enumerate('abcdefghi'))
assert s.count(old)==1;field.write_text(s.replace(old,new));m['files'][str(field.relative_to(dst))]=sha(field)
m['r25_reduction_array']={'control_manifest_sha256':sha(src/'r18-stage.json'),'nine_original_reducer_calls_retained':True,'changed_arithmetic':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
