#!/usr/bin/env python3
"""Align DIF/DIT convolution spectra without runtime bit-reversal passes."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS, one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
assert not a.output.exists()
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
meta=json.loads((a.output/'r17-sbf-probe.json').read_text())
changes={}
for name,expected in [('r17_fast_g.rs',meta['fixed_fft']['r17_fast_g.rs']['after_sha256']),
    ('r17_hybrid_merge.rs',meta['hybrid_merge_files']['r17_hybrid_merge.rs'])]:
    path=root/name;before=path.read_bytes()
    assert hashlib.sha256(before).hexdigest()==expected
    s=before.decode()
    if name=='r17_fast_g.rs':
        s=one_replace(s,'include!("r17_fast_g_tables.rs");',
            'include!("r17_fast_g_tables.rs");\ninclude!("r17_aligned_fft.rs");','aligned helper')
        start=s.index('pub(super) fn apply(');end=s.index('\n#[cfg',start+20)
        # The first cfg inside apply is indented, so the unindented match ends apply.
        part=s[start:end].replace('fft(&mut work,','aligned_fft(&mut work,').replace('INVERSE_SPECTRUM[i]','ALIGNED_INVERSE[i]')
        s=s[:start]+part+s[end:]
        s=one_replace(s,'pub(super) fn check() {','pub(super) fn check() {\n    check_aligned_fft();','new arithmetic/permutation gate')
    else:
        runtime,host=s.split('#[cfg(not(performance_sbf))]',1)
        runtime=runtime.replace('fft(left,','aligned_fft(left,').replace('fft(right,','aligned_fft(right,').replace('MERGE_SPECTRA[','ALIGNED_MERGE[')
        s=runtime+'#[cfg(not(performance_sbf))]'+host
    assert s!=before.decode()
    path.write_text(s)
    changes[name]={'before_sha256':expected,'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
meta['aligned_fft']=changes
meta['aligned_fft_files']={}
for name in ['r17_aligned_fft.rs','r17_aligned_generate.rs']:
    data=Path(__file__).with_name(name).read_bytes();(root/name).write_bytes(data)
    meta['aligned_fft_files'][name]=hashlib.sha256(data).hexdigest()
manifest=root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text()+'\n[[bin]]\nname="r17-aligned-generate"\npath="../r17_aligned_generate.rs"\n')
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
