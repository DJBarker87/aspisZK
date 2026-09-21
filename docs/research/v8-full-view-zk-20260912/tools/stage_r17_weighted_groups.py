#!/usr/bin/env python3
"""Extend the R29 control with weighted-prefix contraction; caller unchanged."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS,one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--repo',type=Path,required=True)
a=p.parse_args()
assert not a.output.exists()
meta=json.loads((a.stage/'r17-compact-control.json').read_text())
for name,expected in meta['files'].items():
    assert hashlib.sha256((a.stage/EXPERIMENTS/name).read_bytes()).hexdigest()==expected
source=(a.repo/EXPERIMENTS/'structured_weights.rs').read_text()
staged=(a.stage/EXPERIMENTS/'structured_weights.rs').read_text()
start=source.index('fn basis(')
end=source.index('    let mut distinct = Vec::<u16>::new();',start)
body=source[start:end]
assert body==staged[staged.index('fn basis('):staged.index('    let mut distinct = Vec::<u16>::new();')]
body=one_replace(body,
    'fn grouped_terminal(masks: &[u16; 64], [a, b, c]: [K; 3], alpha: [K; 4]) -> ([K; 4], usize, usize) {',
    'fn geometry([a,b,c]:[K;3],alpha:[K;4])->([K;16],[K;3],[K;16]) {',
    'retain exact local geometry body')
body+='''    #[cfg(v8_grouped_linear)]
    let normal=core::array::from_fn(|j|corelib::field::qm31_sum_products3_prepared(
        &prepared_chord,&[low[j],xn[j],yn[j]]));
    let _=products;
    (normal,[carry[0],carry[1],carry[2]],high)
}
'''
edge_source=(a.repo/EXPERIMENTS/'inactive_row_binding.rs').read_text()
start=edge_source.index('fn edges(');end=edge_source.index('\n#[cfg',start)
edges=edge_source[start:end]+'\n'
staged_edges=(a.stage/EXPERIMENTS/'inactive_row_binding.rs').read_text()
assert edges==staged_edges[staged_edges.index('fn edges('):staged_edges.index('\n#[cfg',staged_edges.index('fn edges('))]+'\n'
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
(root/'r17_reused_group_geometry.rs').write_text(edges+body)
name='r17_weighted_groups.rs'
(root/name).write_bytes(Path(__file__).with_name(name).read_bytes())
path=root/'r17_compact_transport_check.rs'
s=path.read_text()
s=one_replace(s,'mod r17_owned_weights;','mod r17_owned_weights;\nmod r17_weighted_groups;','new kernel')
s=one_replace(s,'let mut delta=vec![K::ZERO;1024];','let mut delta=vec![K::ZERO;479];','bounded correction support')
s=one_replace(s,'''    let others:Vec<_>=t.order.iter().map(|&r|
        if r!=1023 && t.inactive[r] {K::ONE} else {K::ZERO}).collect();
    let pivot:Vec<_>=t.order.iter().map(|&r|if r==1023 {K::ONE}else{K::ZERO}).collect();
    let d=dense_terminal(delta,abc,alpha);
    let o=dense_terminal(others,abc,alpha);
    let p=dense_terminal(pivot,abc,alpha);''','''    let kernel=r17_weighted_groups::Kernel::new(abc,alpha);
    let masks=core::array::from_fn(|group| {
        let mut mask=0u16;
        for j in 0..16 {let r=t.order[16*group+j];if r!=1023 && t.inactive[r] {mask|=1<<j;}}
        mask
    });
    let d=kernel.prefix(&delta);
    let o=kernel.binary_masks(&masks);
    let p=kernel.coordinate(1023);''','use weighted prefix and fixed binary mask contraction')
s=one_replace(s,'    for case in 0..32u32 {','''    for case in 0..3u32 {
        let abc=core::array::from_fn(|i|sample(case*3+i as u32+10));
        let alpha=core::array::from_fn(|i|if case==0 {K::ZERO} else if case==1 {K::ONE} else {sample(i as u32+90)});
        let kernel=r17_weighted_groups::Kernel::new(abc,alpha);
        for row in 0..1024 {
            let mut unit=vec![K::ZERO;1024];unit[row]=K::ONE;
            assert_eq!(kernel.coordinate(row),dense_terminal(unit,abc,alpha));
        }
        for len in [0usize,1,2,3,15,16,17,31,32,33,255,256,257,478,479,480,511,512,513,1023,1024] {
            let values:Vec<_>=(0..len).map(|j|sample((len+j) as u32)).collect();
            let mut padded=values.clone();padded.resize(1024,K::ZERO);
            assert_eq!(kernel.prefix(&values),dense_terminal(padded,abc,alpha));
        }
        for case in 0..16u16 {
            let masks=core::array::from_fn(|j|if case==0 {0} else if case==1 {u16::MAX} else {(j as u16).wrapping_mul(119).wrapping_add(case*179)});
            let values=(0..1024).map(|j|if masks[j/16]&(1<<(j%16))!=0 {K::ONE}else{K::ZERO}).collect();
            assert_eq!(kernel.binary_masks(&masks),dense_terminal(values,abc,alpha));
        }
    }
    println!("PASS: 3072 coordinate controls, 63 arbitrary-prefix boundary controls, 48 binary-mask controls; all four terminal entries equal dense source");
    for case in 0..32u32 {''','whole support and boundary controls')
s=one_replace(s,'//! Dense correction contraction here is an oracle, NOT an optimized verifier.',
    '//! Sparse correction candidate compared against the unchanged dense source oracle.','scope')
s=one_replace(s,'BOUNDARY: correction contraction remains dense in this control; no SBF CU claim, transcript change, verifier integration, source extraction or privacy theorem',
    'BOUNDARY: weighted correction contraction is source-tested; no SBF CU claim, transcript change, verifier integration, source extraction or privacy theorem','boundary')
path.write_text(s)
for name in ['r17_reused_group_geometry.rs','r17_weighted_groups.rs','r17_compact_transport_check.rs','inactive_row_binding.rs']:
    meta['files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
meta['source_base']='b453b56a'
meta['scope']='weighted prefix and binary-mask contraction reusing pinned baseline low/carry geometry; host only'
(a.output/'r17-compact-control.json').write_text(json.dumps(meta,indent=2)+'\n')
