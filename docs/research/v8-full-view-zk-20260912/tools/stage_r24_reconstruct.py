#!/usr/bin/env python3
"""Flatten the linear nine-channel reconstruction after canonical reduction."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==183 and 'r24_prepared' in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
field=dst/'crates/aspis-core/src/field.rs';text=field.read_text();start=text.index('fn qm31_from_karatsuba_channel_sums(');end=text.index('\n/// Sum up to four QM31 products',start)
old=text[start:end]
assert old.count('let m0 = reconstruct(sums[0]);')==1
new='''fn qm31_from_karatsuba_channel_sums(sums: [[u64; 3]; 3]) -> QM31 {
    let r=sums.map(|row|row.map(|x|u64::from(M31::reduce_u64(x).0)));
    let [a,b,c,d,e,f,g,h,i]=[r[0][0],r[0][1],r[0][2],r[1][0],r[1][1],r[1][2],r[2][0],r[2][1],r[2][2]];
    let p=u64::from(P);
    // Every r is canonical for ANY u64 input channel. The P offsets dominate
    // all negative terms; every intermediate is nonnegative and <10P<2^35.
    // Offsets vanish modulo P. No challenge or input-validity premise added.
    let x=a.wrapping_add(3*d).wrapping_add(3*p).wrapping_sub(b).wrapping_sub(e).wrapping_sub(f);
    let y=c.wrapping_add(2*f).wrapping_add(6*p).wrapping_sub(a).wrapping_sub(b).wrapping_sub(d).wrapping_sub(3*e);
    let z=g.wrapping_add(b).wrapping_add(e).wrapping_add(3*p).wrapping_sub(h).wrapping_sub(a).wrapping_sub(d);
    let t=i.wrapping_add(a).wrapping_add(b).wrapping_add(d).wrapping_add(e).wrapping_add(4*p).wrapping_sub(g).wrapping_sub(h).wrapping_sub(c).wrapping_sub(f);
    QM31{c0:CM31::new(M31::reduce_u64(x),M31::reduce_u64(y)),c1:CM31::new(M31::reduce_u64(z),M31::reduce_u64(t))}
}
'''
field.write_text(text[:start]+new+text[end:])
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';test=ex/'r23_field_check.rs';text=test.read_text()
old='''        let ar=reference(a);let br=reference(b);'''
new=old+'''
        use aspis_core::field as f;
        let aa=[a,b,a.neg(),b.neg()];let bb=[b,a,b.neg(),a.neg()];
        let ra=[ar,br,ar.neg(),br.neg()];let rb=[br,ar,br.neg(),ar.neg()];
        let comparisons=[
            (f::qm31_sum_products2([aa[0],aa[1]],[bb[0],bb[1]]),r23_reference_field::qm31_sum_products2([ra[0],ra[1]],[rb[0],rb[1]])),
            (f::qm31_sum_products3([aa[0],aa[1],aa[2]],[bb[0],bb[1],bb[2]]),r23_reference_field::qm31_sum_products3([ra[0],ra[1],ra[2]],[rb[0],rb[1],rb[2]])),
            (f::qm31_sum_products4(aa,bb),r23_reference_field::qm31_sum_products4(ra,rb))];
        for (x,y) in comparisons {let mut bytes=[0;16];y.write_le_bytes(&mut bytes);assert_eq!(encode(x),bytes);}
'''
assert text.count(old)==1;text=text.replace(old,new)
text=text.replace('operations_per_pair=3','operations_per_pair=6 dot_arities=2,3,4')
test.write_text(text)
for path in [field,test]:m['files'][str(path.relative_to(dst))]=sha(path)
m['r24_reconstruct']={'control_manifest_sha256':sha(src/'r18-stage.json'),'input_channels':'arbitrary u64; reduce each canonically before reconstruction','linear_reconstruction_flattened':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
