#!/usr/bin/env python3
"""Same R18 source-screened profile, sparse/shared compact primary.

All dense reference checks stay. Primary-only harness is a distinct later mode.
"""
import argparse,hashlib,json,shutil
from pathlib import Path
from reconstruct_generated_inputs import EXPERIMENTS,one_replace

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();assert not a.output.exists()
meta=json.loads((a.stage/'r18-stage.json').read_text())
assert meta['current_T_unchanged'] and not meta['compact_primary']
for name,expected in meta['files'].items():assert sha(a.stage/name)==expected,name
shutil.copytree(a.stage,a.output);root=a.output/EXPERIMENTS
changes={}
def edit(name,transform):
    path=root/name;before=sha(path);path.write_text(transform(path.read_text()))
    changes[name]=dict(before_sha256=before,after_sha256=sha(path))
edit('relation_callback.rs',lambda s:one_replace(s,'mod r18_sparse_coded_g;',
    'mod r18_sparse_coded_g;\nmod r18_compact_g;\nmod r18_shared_ordinary;','compact sparse modules'))

def relation(s):
    start=s.index('        if channel==0 && !dense_ordinary {')
    end=s.index('\n#[cfg(target_os="solana")]',start)
    s=s[:start]+'''        if !dense_ordinary {
            let mut pair=crate::r17_compact_prepare::ordinary_pair(&s.z,kappa,use_x);
            if channel==1 {
                let e=crate::r18_compact_g::first_pair(&s.z,use_x);
                for j in 0..2 {pair[j]=pair[j].sub(kappa.mul(e[j]));}
                // Sparse H is in code coordinates 128,131,...,938: its
                // constant/x/y entries are identically zero, for every z.
            }
            let i=if channel==0 {iv}else{iv_g};
            claim=claim.sub(i[0].mul(pair[0])).sub(i[1].mul(pair[1]));
            if channel==0 {ordinary[0]=vec![K::ZERO;1024];}
            continue;
        }
'''+s[end:]
    s=one_replace(s,'    let weights = [(0, ordinary0), (1, ordinary1)].map(|(channel, mut v)| {',
        '''    let weights = [(0, ordinary0), (1, ordinary1)].map(|(channel, mut v)| {
        if channel==1 && !dense_ordinary {return WeightAccumulator::empty(10);}''','query-only G')
    s=one_replace(s,'''        } else {
            weights[c].fold_deferred_relation_arity4(a);
        }
    }

    #[cfg(target_os="solana")] { solana_program::msg!("R17:first-fold-end");''',
        '''        } else {
            weights[c]=WeightAccumulator::empty(8);
        }
    }

    #[cfg(target_os="solana")] { solana_program::msg!("R17:first-fold-end");''','retain fresh-query chronology')
    start=s.index('    let terminal = (0..2).fold(K::ZERO, |s,c| {')
    end=s.index('    if terminal != claim {',start)
    s=s[:start]+'''    let mut terminal=(0..2).fold(K::ZERO,|sum,c| {
        let w=if reference {core::array::from_fn(|i|dense[c][i])}
              else {weights[c].weight_prefix::<4>()};
        sum.add(corelib::field::qm31_sum_products4(w,core::array::from_fn(|i|finals[c][i])))
    });
    if !reference {
        #[cfg(target_os="solana")] { solana_program::msg!("R18:shared-ordinary-start"); solana_program::log::sol_log_compute_units(); }
        let [ordinary,first]=crate::r18_shared_ordinary::terminal_pair(
            &public_audit,p.abc,ordinary_alphas,&mut ordinary_workspace);
        #[cfg(target_os="solana")] { solana_program::msg!("R18:shared-ordinary-end"); solana_program::log::sol_log_compute_units(); }
        let z=core::array::from_fn(|i|public_audit[i]);
        let sparse=crate::r18_compact_g::terminal(&z,p.abc,ordinary_alphas,&mut ordinary_workspace);
        #[cfg(target_os="solana")] { solana_program::msg!("R18:sparse-G-end"); solana_program::log::sol_log_compute_units(); }
        terminal=terminal.add(corelib::field::qm31_sum_products4(ordinary,
            core::array::from_fn(|i|finals[0][i].add(finals[1][i]))));
        terminal=terminal.add(public_audit[10].mul(corelib::field::qm31_sum_products4(
            core::array::from_fn(|i|sparse[i].sub(first[i])),core::array::from_fn(|i|finals[1][i]))));
        // Both independent image constraints remain, including invalid inputs.
        let image=image_terminal(p.tau,p.abc[1],p.abc[2],ordinary_alphas);
        terminal=terminal.add(image.mul(finals[0][3])).add(p.tau.square().mul(image).mul(finals[1][3]));
    }
'''+s[end:]
    return s
edit('r17_host_relation.rs',relation)
def harness(s):
    needle='    let result=crate::r17_relation::verify(w,prepared,false);'
    start=s.index(needle)+len(needle)
    end=s.index('\n}',start)
    tail=s[start:end]
    assert 'assert_eq!(result,reference' in tail
    return s[:start]+'''
    #[cfg(all(target_os="solana",r18_primary_only))]
    { return result.map_err(|_|6u32); }
    #[cfg(not(all(target_os="solana",r18_primary_only)))]
    {'''+tail+'\n    }'+s[end:]
edit('performance_verifier.rs',harness)
for name in ['r18_compact_g.rs','r18_shared_ordinary.rs','r18_shared_ordinary_check.rs']:
    shutil.copy2(Path(__file__).with_name(name),root/name)
repo=Path(__file__).resolve().parents[4]
shutil.copy2(repo/'tools/r18_sparse_coded_g_check.rs',root/'r18_sparse_coded_g_check.rs')
manifest=root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text()+'''\n[[bin]]
name="r18-shared-ordinary-check"
path="../r18_shared_ordinary_check.rs"
[[bin]]
name="r18-sparse-coded-g-check"
path="../r18_sparse_coded_g_check.rs"
''')
meta.update(compact_primary=True,compact_changes=changes,sbf_measured=False)
meta['files'].update({str(p.relative_to(a.output)):sha(p) for p in sorted(root.glob('*.rs'))})
(a.output/'r18-stage.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(stage=str(a.output),profile=meta['profile'],same_transcript=True)))
