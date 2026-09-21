#!/usr/bin/env python3
"""Versioned compact binding; omit primary ordinary expansion, keep dense oracle.

Not byte-compatible with research-v1. Both channels remain bound to the full
verifier-derived inputs and exact fixed map. G expansion is still a TODO.
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
meta=json.loads((a.stage/'r17-sbf-probe.json').read_text())
control=json.loads((a.stage/'r17-compact-control.json').read_text())
for name,expected in control['files'].items():
    assert hashlib.sha256((a.stage/EXPERIMENTS/name).read_bytes()).hexdigest()==expected
for name,expected in control['core_files'].items():
    assert hashlib.sha256((a.stage/name).read_bytes()).hexdigest()==expected
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
changes={}
old_profile='AV8/R17/structuredG271-two-channel/research-v1'
profile='AV8/R17/structuredG271-two-channel/compact-binding-research-v2'
for name in ['relation_callback.rs','r17_host_relation.rs','performance_verifier.rs','payment_extraction.rs']:
    path=root/name;before=path.read_bytes();s=before.decode()
    if name=='relation_callback.rs':
        s=one_replace(s,'mod r17_compact_workspace;','mod r17_compact_workspace;\nmod r17_compact_prepare;','compact preparation module')
    elif name=='r17_host_relation.rs':
        assert hashlib.sha256(before).hexdigest()==meta['compact_workspace'][name]['after_sha256']
        s=one_replace(s,'pub(super) fn prepare(s: row::Semantic, w: &Wire<\'_>) -> Result<Prepared, Error> {',
            '''pub(super) fn prepare(s: row::Semantic, w: &Wire<'_>) -> Result<Prepared, Error> {
    prepare_mode(s,w,true)
}
pub(super) fn prepare_compact(s: row::Semantic, w: &Wire<'_>) -> Result<Prepared, Error> {
    prepare_mode(s,w,false)
}
#[inline(never)]
fn prepare_mode(s: row::Semantic, w: &Wire<'_>, dense_ordinary:bool) -> Result<Prepared, Error> {''','separate primary and dense-oracle preparation')
        s=one_replace(s,'    let mut ordinary = [Vec::new(), Vec::new()];\n    for channel in 0..2 {','''    let mut ordinary = [Vec::new(), Vec::new()];
    for channel in 0..2 {
        if channel==0 && !dense_ordinary {
            let pair=crate::r17_compact_prepare::ordinary_pair(&s.z,kappa,use_x);
            claim=claim.sub(iv[0].mul(pair[0])).sub(iv[1].mul(pair[1]));
            // Scratch ONLY: no original, dual, chord or image evaluation.
            // The primary verifier consumes it at its first fold and computes
            // the same ordinary/image functional at the terminal instead.
            ordinary[0]=vec![K::ZERO;1024];
            continue;
        }''','remove primary ordinary expansion')
        s=one_replace(s,'AV8/R17/Vandermonde1024-nodes1to1024/271-coins/two-channel/v1',
            'AV8/R17/compact-functional/Vandermonde1024-nodes1to1024/271-coins/two-channel/v2','new functional descriptor domain')
        start=s.index('    t.absorb(label::PROFILE, &descriptor);')
        end=s.index('    t.absorb(label::CLAIM, &bytes(&[claim]));',start)
        s=s[:start]+'''    // Fixed framing: map above plus every variable functional input.
    // This description is derived by the verifier, never supplied as a hint.
    descriptor.extend([20,22,10,4,4,2,use_x as u8]);
    descriptor.extend(bytes(&s.z));
    descriptor.extend(bytes(&[kappa]));
    descriptor.extend(bytes(&abc));
    descriptor.extend(bytes(&iv));
    descriptor.extend(bytes(&iv_g));
    descriptor.extend(bytes(&[p0.x,p0.y,p1.x,p1.y,gamma]));
    t.absorb(label::PROFILE, &descriptor);
'''+s[end:]
        s=one_replace(s,'AV8/R17/four-image-residuals/v1','AV8/R17/four-image-residuals/compact-binding-v2','image challenge domain')
    else:
        s=one_replace(s,old_profile,profile,'new profile from transcript start')
        if name=='performance_verifier.rs':
            needle='let prepared=crate::r17_relation::prepare(s,w).map_err(|_|5u32)?;'
            assert s.count(needle)==2
            s=s.replace(needle,'let prepared=crate::r17_relation::prepare_compact(s,w).map_err(|_|5u32)?;',1)
    path.write_text(s)
    changes[name]={'before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
meta['compact_prepare']=changes
meta['compact_prepare_files']={}
for name in ['r17_compact_prepare.rs','r17_compact_prepare_check.rs']:
    (root/name).write_bytes(Path(__file__).with_name(name).read_bytes())
    meta['compact_prepare_files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
host=json.loads((a.output/'r17-stage.json').read_text())
for item in [meta,host]:
    item['profile']=profile
    item['transcript_compatible_with_r17_v1']=False
    item['privacy_proved']=False
    item['soundness_preservation_proved']=False
(a.output/'r17-stage.json').write_text(json.dumps(host,indent=2)+'\n')
manifest=root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text()+'\n[[bin]]\nname="r17-compact-prepare-check"\npath="../r17_compact_prepare_check.rs"\n')
for name in list(control['files'])+list(changes)+list(meta['compact_prepare_files']):
    control['files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
control['bin']='r17-compact-prepare-check'
control['scope']='128 actual-source compact claim entries; no allocation after fixed map initialization'
(a.output/'r17-compact-control.json').write_text(json.dumps(control,indent=2)+'\n')
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
