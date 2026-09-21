#!/usr/bin/env python3
"""Connect prefix+full-geometric G evaluation; keep the exact research-v2 map."""
import argparse,hashlib,json,shutil
from pathlib import Path
from reconstruct_generated_inputs import EXPERIMENTS,one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();assert not a.output.exists()
control=json.loads((a.stage/'r17-compact-control.json').read_text())
for name,sha in control['files'].items():
    assert hashlib.sha256((a.stage/EXPERIMENTS/name).read_bytes()).hexdigest()==sha
for name,sha in control.get('core_files',{}).items():
    assert hashlib.sha256((a.stage/name).read_bytes()).hexdigest()==sha
shutil.copytree(a.stage,a.output);root=a.output/EXPERIMENTS
meta=json.loads((a.output/'r17-sbf-probe.json').read_text());changes={}
for name in ['relation_callback.rs','r17_host_relation.rs','r17_compact_workspace.rs']:
    path=root/name;before=path.read_bytes();s=before.decode()
    if name=='relation_callback.rs':
        s=one_replace(s,'mod r17_compact_prepare;','mod r17_compact_prepare;\nmod r17_g_geometric;\nmod r17_compact_g;','complete compact G modules')
    elif name=='r17_compact_workspace.rs':
        s=one_replace(s,'fn fill_tensor(','pub(super) fn fill_tensor(','reuse exact base factor fill')
        s=one_replace(s,'fn entry(','pub(super) fn entry(','reuse exact tensor entry')
    else:
        s=one_replace(s,'    pub(super) claim: K,','    pub(super) claim: K,\n    pub(super) compact_g: Option<crate::r17_compact_g::Description>,','prepared G description')
        s=one_replace(s,'    let mut ordinary = [Vec::new(), Vec::new()];','    let mut compact_g=None;\n    let mut ordinary = [Vec::new(), Vec::new()];','G ownership')
        s=one_replace(s,'    for channel in 0..2 {\n        if channel==0 && !dense_ordinary {','''    for channel in 0..2 {
        if channel==1 && !dense_ordinary {
            #[cfg(target_os="solana")] { solana_program::msg!("R17:compact-G-prepare-start"); solana_program::log::sol_log_compute_units(); }
            let audit=core::array::from_fn(|i|if i<10 {s.z[i]}else{kappa});
            let d=crate::r17_compact_g::Description::new(&audit);
            let pair=d.dual_pair(use_x);
            claim=claim.sub(iv_g[0].mul(pair[0])).sub(iv_g[1].mul(pair[1]));
            compact_g=Some(d);
            #[cfg(target_os="solana")] { solana_program::msg!("R17:compact-G-prepare-end"); solana_program::log::sol_log_compute_units(); }
            continue;
        }
        if channel==0 && !dense_ordinary {''','remove G original/dual/chord expansion')
        s=one_replace(s,'    let weights = [(0, ordinary0), (1, ordinary1)].map(|(channel, mut v)| {','''    let weights = [(0, ordinary0), (1, ordinary1)].map(|(channel, mut v)| {
        if channel==1 && !dense_ordinary {return WeightAccumulator::empty(10);}''','query-only primary G accumulator')
        s=one_replace(s,'        iv_g,\n        weights,\n        claim,','        iv_g,\n        weights,\n        claim,\n        compact_g,','return exact compact G description')
        s=one_replace(s,'        mut weights,\n        mut claim,\n    } = prepared;','        mut weights,\n        mut claim,\n        compact_g,\n    } = prepared;','consume G description once')
        s=one_replace(s,'''        } else {
            weights[c].fold_deferred_relation_arity4(a);
        }
    }

    #[cfg(target_os="solana")] { solana_program::msg!("R17:first-fold-end");''','''        } else {
            weights[c]=WeightAccumulator::empty(8);
        }
    }

    #[cfg(target_os="solana")] { solana_program::msg!("R17:first-fold-end");''','defer full G functional, keep fresh query terms')
        s=one_replace(s,'    let terminal = (0..2).fold(K::ZERO, |s,c| {','''    let g_terminal=if reference {None}else {
        #[cfg(target_os="solana")] { solana_program::msg!("R17:compact-G-terminal-start"); solana_program::log::sol_log_compute_units(); }
        let value=compact_g.ok_or(Error::Shape)?.terminal(&public_audit,p.abc,ordinary_alphas);
        #[cfg(target_os="solana")] { solana_program::msg!("R17:compact-G-terminal-end"); solana_program::log::sol_log_compute_units(); }
        Some(value)
    };
    let terminal = (0..2).fold(K::ZERO, |s,c| {''','same full G map at actual four challenges')
        s=one_replace(s,'        s.add(corelib::field::qm31_sum_products4','''        if !reference && c==1 {
            let g=g_terminal.unwrap();
            for i in 0..4 {terminal_weights[i]=terminal_weights[i].add(g[i]);}
            // tau^2 * (tau, tau^2) gives the SAME (tau^3,tau^4)
            // image residual. It is not image_terminal(tau^3,...).
            terminal_weights[3]=terminal_weights[3].add(
                p.tau.square().mul(image_terminal(p.tau,p.abc[1],p.abc[2],ordinary_alphas)));
        }
        s.add(corelib::field::qm31_sum_products4''','retain G image residual and arbitrary invalid-proof behavior')
    path.write_text(s);changes[name]={'before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
meta['compact_g']=changes;meta['compact_g_files']={}
for name in ['r17_compact_g.rs','r17_compact_g_check.rs','r17_g_geometric.rs']:
    (root/name).write_bytes(Path(__file__).with_name(name).read_bytes())
    meta['compact_g_files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
manifest=root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text()+'\n[[bin]]\nname="r17-compact-g-check"\npath="../r17_compact_g_check.rs"\n')
for name in list(control['files'])+list(changes)+list(meta['compact_g_files']):
    control['files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
control['bin']='r17-compact-g-check';control['scope']='complete 271-node G functional including full tail, pivot, source map and claim pairs'
(a.output/'r17-compact-control.json').write_text(json.dumps(control,indent=2)+'\n')
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
