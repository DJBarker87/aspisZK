#!/usr/bin/env python3
"""Fresh exact-R18 stage: expose primary-only opening for differential gates.

The SBF opt-out is a distinct cfg and must not be enabled before the source
correspondence and adversarial gate have been reviewed. Host keeps the check.
"""
import argparse, hashlib, json, shutil
from pathlib import Path
from reconstruct_generated_inputs import EXPERIMENTS, one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
assert not a.output.exists()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
meta=json.loads((a.stage/'r18-stage.json').read_text())
assert meta['basis_profile']=='minimum-support-163' and meta['base_coin_scaling']
for name,h in meta['files'].items(): assert sha(a.stage/name)==h,name
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
path=root/'r17_host_relation.rs'; old=path.read_text(); before=sha(path)
anchor='''    let selected_points = circle_norm::Selected::new(queries)?;'''
replacement='''    opened_mode(w,p,iv_g,queries,alpha,
        !cfg!(all(target_os="solana",r19_no_opening_reference)))
}

pub(super) fn opened_mode(
    w: &Wire<'_>, p: &Prefix, iv_g: [K;2], queries: &[u32], alpha: K,
    check_reference: bool,
) -> Result<([Vec<K>;2],Vec<M31>),Error> {
    let selected_points = circle_norm::Selected::new(queries)?;'''
s=one_replace(old,anchor,replacement,'expose literal primary, keep host default')
s=one_replace(s,'    // Retain an independently implemented original combined-opening check.',
    '''    if !check_reference { return Ok((values,xs)); }
    // Retain an independently implemented original combined-opening check.''','post-auth only')
path.write_text(s)
check=Path(__file__).with_name('r19_opening_check.rs')
shutil.copy2(check,root/check.name)
callback=root/'relation_callback.rs'
callback.write_text(one_replace(callback.read_text(),'#[cfg(v8_performance)]\nfn main(){payment_extraction::performance::run();}',
 '#[cfg(all(v8_performance,not(r19_opening_check)))]\nfn main(){payment_extraction::performance::run();}',
 'standalone focused gate, no unrelated test modules')+
 '\n#[cfg(r19_opening_check)]\nmod r19_opening_check;\n#[cfg(r19_opening_check)]\nfn main(){r19_opening_check::run();}\n')
meta['files'].update({str(p.relative_to(a.output)):sha(p) for p in sorted(root.glob('*.rs'))})
meta['r19_opening']={'before_sha256':before,'after_sha256':sha(path),
    'cfg':'r19_no_opening_reference','host_default_reference':True,'source_gate_passed':False}
(a.output/'r18-stage.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({'stage':str(a.output),'profile':meta['profile'],'same_transcript':True}))
