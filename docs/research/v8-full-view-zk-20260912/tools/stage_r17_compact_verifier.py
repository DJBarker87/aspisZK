#!/usr/bin/env python3
"""Use compact ordinary terminal in the primary research verifier only.

Expanded transcript bytes, prover weights, dense reference verifier, G
channel, image residual and fresh-query accumulator are retained.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS,one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
assert not a.output.exists()
control=json.loads((a.stage/'r17-compact-control.json').read_text())
for name,expected in control['files'].items():
    assert hashlib.sha256((a.stage/EXPERIMENTS/name).read_bytes()).hexdigest()==expected
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
meta=json.loads((a.output/'r17-sbf-probe.json').read_text())
changes={}
for name in ['relation_callback.rs','r17_host_relation.rs']:
    path=root/name;before=path.read_bytes();s=before.decode()
    if name=='relation_callback.rs':
        s=one_replace(s,'mod r17_owned_weights;',
            'mod r17_owned_weights;\nmod r17_weighted_groups;\nmod r17_compact_ordinary;',
            'compact ordinary modules')
    else:
        assert hashlib.sha256(before).hexdigest()==meta['owned_primal'][name]['after_sha256']
        s=one_replace(s,'''    claim = evaluate(&first, a);
    for c in 0..2 {''','''    claim = evaluate(&first, a);
    let mut ordinary_alphas=[a,K::ZERO,K::ZERO,K::ZERO];
    for c in 0..2 {''','retain all four actual source challenges')
        s=one_replace(s,'''        } else {
            weights[c].fold_deferred_relation_arity4(a);
        }
    }

    #[cfg(target_os="solana")] { solana_program::msg!("R17:first-fold-end");''','''        } else if c==0 {
            // Expanded weights were bound by prepare. Ordinary/image terms
            // are evaluated compactly at the terminal; fresh queries alone
            // occupy this unchanged eight-variable accumulator.
            weights[c]=WeightAccumulator::empty(8);
        } else {
            weights[c].fold_deferred_relation_arity4(a);
        }
    }

    #[cfg(target_os="solana")] { solana_program::msg!("R17:first-fold-end");''','defer only ordinary channel; keep G fold')
        s=one_replace(s,'''        let a = sample(&mut p.t, false)?;
        claim = evaluate(&poly, a);''','''        let a = sample(&mut p.t, false)?;
        ordinary_alphas[r]=a;
        claim = evaluate(&poly, a);''','record tail challenges without changing chronology')
        s=one_replace(s,'        let terminal_weights = if reference {','        let mut terminal_weights = if reference {','compact plus query terminal')
        s=one_replace(s,'''        } else { weights[c].weight_prefix::<4>() };
        s.add(corelib::field::qm31_sum_products4''','''        } else { weights[c].weight_prefix::<4>() };
        if !reference && c==0 {
            #[cfg(target_os="solana")] { solana_program::msg!("R17:compact-ordinary-start"); solana_program::log::sol_log_compute_units(); }
            let ordinary=crate::r17_compact_ordinary::terminal_from_audit(&public_audit,p.abc,ordinary_alphas);
            for i in 0..4 {terminal_weights[i]=terminal_weights[i].add(ordinary[i]);}
            // Retain the exact baseline image-residual terminal, not an
            // honest-image premise or a dropped high-coefficient check.
            terminal_weights[3]=terminal_weights[3].add(image_terminal(p.tau,p.abc[1],p.abc[2],ordinary_alphas));
            #[cfg(target_os="solana")] { solana_program::msg!("R17:compact-ordinary-end"); solana_program::log::sol_log_compute_units(); }
        }
        s.add(corelib::field::qm31_sum_products4''','retain image residual and fresh queries')
    path.write_text(s)
    changes[name]={'before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
meta['compact_verifier']=changes
name='r17_compact_ordinary.rs';path=root/name
path.write_text(path.read_text()+'''
#[inline(never)]
pub(super) fn terminal_from_audit(audit:&[K;11],abc:[K;3],alpha:[K;4])->[K;4] {
    let z=core::array::from_fn(|i|audit[i]);
    Description::new(&z,audit[10]).terminal(abc,alpha)
}
''')
meta['compact_verifier_files']={name:hashlib.sha256((root/name).read_bytes()).hexdigest()
    for name in ['r17_compact_ordinary.rs','r17_weighted_groups.rs','r17_reused_group_geometry.rs','r17_reused_block_terminal.rs']}
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
