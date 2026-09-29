#!/usr/bin/env python3
"""Gather identical correction sums for R59 dot; no pair-kernel candidate."""
import argparse,ast,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--checked-dot',action='store_true');a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='088877fa9a02692519479254d348a0eebeaf379bea538b246ee8550b9ba92e8d'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==197
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments'
support=ast.literal_eval(re.search(r'SUPPORT: \[usize;163\] = (\[.*?\]);',(ex/'r18_minimal_support.rs').read_text())[1])
assert len(support)==len(set(support))==163
rows=[];groups=[];ends=[0]
for low in range(19):
    for i,row in enumerate(support):
        if row%16==(low if low<16 else low-16):rows.append(i);groups.append(row//16+(0 if low<16 else 64))
    ends.append(len(rows))
assert max(b-a for a,b in zip(ends,ends[1:]))<=30 and len(rows)==181
tables='\n'.join(f'const R62_{n}:[usize;{len(v)}]={v};'for n,v in [('ENDS',ends),('ROWS',rows),('GROUPS',groups)])+'\n'
helper=(here/'r62_gather.rs').read_text()
if a.checked_dot:
    old='out[low]=corelib::field::qm31_dot(&left[..n],&right[..n]);'
    assert helper.count(old)==1
    helper=helper.replace(old,'out[low]=corelib::field::r25_checked_dot(&left[..n],&right[..n])\n            .unwrap_or_else(||corelib::field::qm31_dot(&left[..n],&right[..n]));')
path=ex/'r19_channel_ordinary.rs';path.write_text(path.read_text()+'\n'+tables+helper)
scalar=ex/'r22_scalar.rs';s=scalar.read_text()
old='''    for i in 0..163 {
        let row=SUPPORT[i];let group=row>>4;let low=row&15;let value=delta[i];
        selected[low]=selected[low].add(value.mul(hb[group]));
        if low<3 {selected[16+low]=selected[16+low].add(value.mul(hb[64+group]));}
    }'''
assert s.count(old)==1 and s.count('    let wp=entry(factors,0,1023);')==1
s=s.replace('    let wp=entry(factors,0,1023);\n','')
s=s.replace(old,'    let wp=entry(factors,0,1023);\n    r62_gather(delta,hb,factors,&mut selected);')
scalar.write_text(s)
native=ex/'r27_native.rs';s=native.read_text();old='r19_channel_ordinary::r27_tensor_check(x);';assert s.count(old)==1
native.write_text(s.replace(old,old+'r19_channel_ordinary::r62_gather_check(x);'))
check=ex/'r27_check.rs';s=check.read_text();assert s.count('R27_SPARSE source_vectors=256')==1
check.write_text(s.replace('R27_SPARSE source_vectors=256','R62_GATHER gathered_outputs=4864 source_vectors=256'))
for f in [path,scalar,native,check]:m['files'][str(f.relative_to(dst))]=sha(f)
m['r62_gather']={'base_revision':'23cf1bd882ccce6f330a4cafb6d39e54c748b984','control_manifest_sha256':sha(src/'r18-stage.json'),
    'reference_entry_unchanged':True,'products':181,'outputs':19,'max_dot_terms':max(b-a for a,b in zip(ends,ends[1:])),
    'scratch_reuses_dead_factors':True,'checked_dot':a.checked_dot,'protocol_changed':False,'validation_removed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
