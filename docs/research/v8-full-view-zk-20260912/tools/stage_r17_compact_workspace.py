#!/usr/bin/env python3
"""Move the consumed ordinary weights into a zero-allocation terminal workspace."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS,one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--implementation',type=Path,
    default=Path(__file__).with_name('r17_compact_workspace.rs'))
a=p.parse_args()
assert not a.output.exists()
meta=json.loads((a.stage/'r17-sbf-probe.json').read_text())
control=json.loads((a.stage/'r17-compact-control.json').read_text())
for name,expected in control['files'].items():
    assert hashlib.sha256((a.stage/EXPERIMENTS/name).read_bytes()).hexdigest()==expected
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
changes={}
for name in ['relation_callback.rs','r17_host_relation.rs','r17_weighted_groups.rs','r17_reused_group_geometry.rs']:
    path=root/name;before=path.read_bytes();s=before.decode()
    if name=='relation_callback.rs':
        s=one_replace(s,'mod r17_compact_ordinary;','mod r17_compact_ordinary;\nmod r17_compact_workspace;','workspace module')
    elif name=='r17_host_relation.rs':
        s=one_replace(s,'    let mut ordinary_alphas=[a,K::ZERO,K::ZERO,K::ZERO];',
            '    let mut ordinary_alphas=[a,K::ZERO,K::ZERO,K::ZERO];\n    let mut ordinary_workspace=Vec::new();','owned workspace')
        s=one_replace(s,'            weights[c]=WeightAccumulator::empty(8);',
            '''            ordinary_workspace=core::mem::replace(&mut weights[c],WeightAccumulator::empty(8))
                .into_single_dense_for_workspace().ok_or(Error::Shape)?;''','move instead of dropping consumed dense buffer')
        s=one_replace(s,'crate::r17_compact_ordinary::terminal_from_audit(&public_audit,p.abc,ordinary_alphas)',
            'crate::r17_compact_workspace::terminal(&public_audit,p.abc,ordinary_alphas,&mut ordinary_workspace)',
            'borrow consumed ordinary buffer at terminal')
    elif name=='r17_weighted_groups.rs':
        s+='\ninclude!("r17_workspace_group_methods.rs");\n'
    else:
        s=one_replace(s,'fn edges(j:usize)->Vec<(usize,M31)>',
            '#[cfg(not(target_os="solana"))]\nfn edges_reference(j:usize)->Vec<(usize,M31)>','retain exact old edge reference')
        s='include!("r17_edges_iter.rs");\n'+s
    path.write_text(s)
    changes[name]={'before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
meta['compact_workspace']=changes
meta['compact_workspace_files']={}
for name in ['r17_compact_workspace.rs','r17_compact_workspace_check.rs','r17_workspace_group_methods.rs','r17_edges_iter.rs']:
    source=a.implementation if name=='r17_compact_workspace.rs' else Path(__file__).with_name(name)
    path=root/name;path.write_bytes(source.read_bytes())
    meta['compact_workspace_files'][name]=hashlib.sha256(path.read_bytes()).hexdigest()
probe=Path(__file__).parent/'r17-mask-extraction/workspace_probe.rs'
source=probe.read_text();start=source.index('use std::alloc::');end=source.index('\nfn main()',start)
name='r17_reused_deny_allocator.rs';(root/name).write_text(source[start:end]+'\n')
meta['compact_workspace_files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
meta['compact_workspace_allocator_source_sha256']=hashlib.sha256(probe.read_bytes()).hexdigest()
core=a.output/'crates/aspis-core/src/sumcheck.rs';before=core.read_bytes()
assert hashlib.sha256(before).hexdigest()==meta['inplace_dense_fold']['after_sha256']
s=one_replace(before.decode(),'impl WeightAccumulator {','''impl WeightAccumulator {
    /// Research-only ownership handoff after this dense covector is bound.
    /// No copies, field changes, or allocation; non-single-dense shapes fail.
    #[cfg(v8_compact_workspace)]
    pub fn into_single_dense_for_workspace(mut self) -> Option<Vec<QM31>> {
        if self.components.len()!=1 {return None;}
        match self.components.pop()? {
            WeightComponent::Dense {values} => Some(values),
            _ => None,
        }
    }
''','isolated ownership-only dense accessor')
core.write_text(s)
meta['compact_workspace_core']={'path':'crates/aspis-core/src/sumcheck.rs',
    'before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':hashlib.sha256(core.read_bytes()).hexdigest()}
host=json.loads((a.output/'r17-stage.json').read_text())
for item in [meta,host]:
    assert '--cfg v8_compact_workspace' not in item['rustflags']
    item['rustflags']+=' --cfg v8_compact_workspace'
(a.output/'r17-stage.json').write_text(json.dumps(host,indent=2)+'\n')
manifest=root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text()+'\n[[bin]]\nname="r17-compact-workspace-check"\npath="../r17_compact_workspace_check.rs"\n')
for name in list(control['files'])+list(meta['compact_workspace_files']):
    control['files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
control['core_files']={'crates/aspis-core/src/sumcheck.rs':meta['compact_workspace_core']['after_sha256']}
control['bin']='r17-compact-workspace-check'
control['scope']='allocation-denied terminal in moved single-dense workspace, source and shape controls'
(a.output/'r17-compact-control.json').write_text(json.dumps(control,indent=2)+'\n')
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
