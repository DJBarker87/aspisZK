#!/usr/bin/env python3
"""Restore retained baseline opening/fold kernels to the R17 caller; no new profile."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS, one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--repo',type=Path,required=True)
a=p.parse_args()
assert not a.output.exists()
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
meta=json.loads((a.output/'r17-sbf-probe.json').read_text())
host=json.loads((a.output/'r17-stage.json').read_text())
assert 'aligned_fft' not in meta and 'fused_reorder' not in meta
reused={}
for name in ['circle_norm.rs','joined_inverse.rs','line_norm.rs','quotient_fold.rs','affine_primal.rs']:
    data=(a.repo/EXPERIMENTS/name).read_bytes()
    assert (root/name).read_bytes()==data,'reuse the retained source, not a replacement'
    reused[name]=hashlib.sha256(data).hexdigest()
flags=['v8_circle_norm','v8_chord_norm','v8_joined_inverse','v8_split_inverse','v8_line_norm','v8_quotient_fused','v8_affine_primal']
meta['baseline_reuse_flags']={'host_before':host['rustflags'],'sbf_before':meta['rustflags'],'added':flags}
for item in [host,meta]:
    for flag in flags:
        assert '--cfg '+flag not in item['rustflags']
        item['rustflags']+=' --cfg '+flag
path=root/'r17_host_relation.rs';before=path.read_bytes()
assert hashlib.sha256(before).hexdigest()==meta['inplace_fold_relation'][path.name]['after_sha256']
s=one_replace(before.decode(),'''    let pts = corelib::circle_fri::selected_circle_fiber_points_shared(20, queries)
        .map_err(|_| Error::Domain)?;''','''    let selected_points = circle_norm::Selected::new(queries)?;
    let pts = selected_points.points();
    let mut denoms = Vec::with_capacity(4*queries.len());
    let mut base_denoms = Vec::with_capacity(2*queries.len());
    let mut lines = Vec::with_capacity(queries.len());
    for base in pts {
        base_denoms.extend([base.x.double(),base.y.double()]);
        lines.push(base.x.mul(base.x).double().sub(M31::ONE));
        for (x,y) in [(base.x,base.y),(base.x,base.y.neg()),(base.x.neg(),base.y.neg()),(base.x.neg(),base.y)] {
            denoms.push(p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y)));
        }
    }
    // Exact baseline helper; same internally selected points/chord/line values.
    // Both channels share the denominator, so invert this list only once.
    // A batch failure is not returned here: preserve the original per-record
    // canonical/domain failure ordering via the individual fallback below.
    let inverse_batch=selected_points.inverse_lines(&denoms,p.abc,&base_denoms,&lines);
    let prepared_fold=quotient_fold::Prepared::new(alpha);''','reuse checked line geometry/inversion')
s=one_replace(s,'                let denom = p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y));\n','', 'shared denominator')
s=one_replace(s,'.mul(denom.try_inv().ok_or(Error::Domain)?);','''.mul(match &inverse_batch {
                        Ok((inverses,_))=>inverses[4*i+slot],
                        Err(_)=>denoms[4*i+slot].try_inv().ok_or(Error::Domain)?,
                    });''','reuse the common inverse without moving failures')
s=one_replace(s,'''            values[channel].push(corelib::field::qm31_circle_to_line_fold4(
                q,
                alpha,
                base.x.double().inv(),
                base.y.double().inv(),
            ));''','''            let (ix,iy)=match &inverse_batch {
                Ok((_,base_inverses))=>(base_inverses[2*i],base_inverses[2*i+1]),
                Err(_)=>(base.x.double().inv(),base.y.double().inv()),
            };
            let folded=prepared_fold.fold(q,ix,iy);
            #[cfg(not(target_os="solana"))]
            assert_eq!(folded,corelib::field::qm31_circle_to_line_fold4(q,alpha,base.x.double().inv(),base.y.double().inv()));
            values[channel].push(folded);''','reuse proved quotient fold')
s=one_replace(s,'        xs.push(base.x.mul(base.x).double().sub(M31::ONE));','        xs.push(lines[i]);','reuse exact line coordinate')
start=s.index('    let terminal = (0..2).fold(')
end=s.index('\n    if terminal != claim',start)
s=s[:start]+'''    let terminal = (0..2).fold(K::ZERO, |s,c| {
        let terminal_weights = if reference {
            core::array::from_fn(|i|dense[c][i])
        } else { weights[c].weight_prefix::<4>() };
        s.add(corelib::field::qm31_sum_products4(terminal_weights,
            core::array::from_fn(|i|finals[c][i])))
    });'''+s[end:]
path.write_text(s)
meta['baseline_reuse']={path.name:{'before_sha256':hashlib.sha256(before).hexdigest(),
    'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}}
meta['baseline_reuse_files']=reused
callback=(root/'relation_callback.rs').read_text()
start=callback.index('fn batch_inverse_m(');end=callback.index('\n#[inline(never)]',start)
(root/'r17_reused_batch_inverse.rs').write_text(callback[start:end]+'\n')
name='r17_baseline_reuse_check.rs';(root/name).write_bytes(Path(__file__).with_name(name).read_bytes())
for name in ['r17_reused_batch_inverse.rs','r17_baseline_reuse_check.rs']:
    meta['baseline_reuse_files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
manifest=root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text()+'\n[[bin]]\nname="r17-baseline-reuse-check"\npath="../r17_baseline_reuse_check.rs"\n')
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
(a.output/'r17-stage.json').write_text(json.dumps(host,indent=2)+'\n')
