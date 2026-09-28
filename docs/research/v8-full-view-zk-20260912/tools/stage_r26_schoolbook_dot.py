#!/usr/bin/env python3
"""Exact-profile whole-dot experiment, retaining validation and old oracle."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);g=p.add_mutually_exclusive_group();g.add_argument('--unroll',action='store_true');g.add_argument('--lane-major',action='store_true');a=p.parse_args();src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==180 and 'r25_reduction_array'in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists() and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
helper=dst/'crates/aspis-core/src/r25_checked_dot.rs';shutil.copy2(here/'r26_schoolbook_dot.rs',helper)
if a.unroll:
    s=helper.read_text()
    start=s.index('        for i in 0..4 {for j in 0..4 {');end=s.index('\n        if index&3==3',start)
    s=s[:start]+'\n'.join(f'        raw[{4*i+j}]=raw[{4*i+j}].wrapping_add(u64::from(x[{i}])*u64::from(y[{j}]));'for i in range(4)for j in range(4))+s[end:]
    start=s.index('            for k in 0..16 {');end=s.index('\n        }',start)
    s=s[:start]+'\n'.join(f'            partial[{k}]=partial[{k}].wrapping_add((raw[{k}]&u64::from(P)).wrapping_add(raw[{k}]>>31)); raw[{k}]=0;'for k in range(16))+s[end:]
    old='    for k in 0..16 {partial[k]=u64::from(M31::reduce_u64(partial[k]).0);}'
    assert s.count(old)==1;s=s.replace(old,'\n'.join(f'    partial[{k}]=u64::from(M31::reduce_u64(partial[{k}]).0);'for k in range(16)))
    helper.write_text(s)
if a.lane_major:
    s=helper.read_text();start=s.index('    let mut raw=');end=s.index('    let [ae,',start)
    lanes=['c0.a','c0.b','c1.a','c1.b']
    body='''    // Validate once before all pure immutable-array passes. The same inputs
    // are rejected even if another factor is zero; no callback is reordered.
    for (&a,&b) in left.iter().zip(right) {
        let x=[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0,b.c0.a.0,b.c0.b.0,b.c1.a.0,b.c1.b.0];
        if x.iter().any(|&v|v>=P){return None;}
    }
    macro_rules! lane { ($lh:ident.$ll:ident,$rh:ident.$rl:ident) => {{
        let mut raw=0u64;let mut partial=0u64;
        for (index,(a,b)) in left.iter().zip(right).enumerate() {
            raw=raw.wrapping_add(u64::from(a.$lh.$ll.0)*u64::from(b.$rh.$rl.0));
            if index&3==3 {partial=partial.wrapping_add((raw&u64::from(P)).wrapping_add(raw>>31));raw=0;}
        }
        if left.len()&3!=0 {partial=partial.wrapping_add((raw&u64::from(P)).wrapping_add(raw>>31));}
        u64::from(M31::reduce_u64(partial).0)
    }}; }
    let partial=[
'''+',\n'.join(f'        lane!({x},{y})'for x in lanes for y in lanes)+'];\n'
    helper.write_text(s[:start]+body+s[end:])
m['files'][str(helper.relative_to(dst))]=sha(helper)
m['r26_schoolbook_dot']={'control_manifest_sha256':sha(src/'r18-stage.json'),'channels':16,'group_terms':4,'max_terms':4096,'canonical_validation_retained':True,'original_dot_oracle_retained':True,'explicit_unroll':a.unroll,'lane_major':a.lane_major}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
