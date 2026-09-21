#!/usr/bin/env python3
"""Replace oversized stack tables and duplicate correction storage after R32."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
assert not a.output.exists()
meta=json.loads((a.stage/'r17-sbf-probe.json').read_text())
for name,expected in meta['compact_verifier_files'].items():
    assert hashlib.sha256((a.stage/EXPERIMENTS/name).read_bytes()).hexdigest()==expected
control=json.loads((a.stage/'r17-compact-control.json').read_text())
for name,expected in control['files'].items():
    data=(a.stage/EXPERIMENTS/name).read_bytes()
    if name in meta['compact_verifier']:
        change=meta['compact_verifier'][name]
        assert change['before_sha256']==expected
        expected=change['after_sha256']
    elif name=='r17_compact_ordinary.rs':
        # R32 appended only the audited wrapper to the R31 helper.
        marker='\n#[inline(never)]\npub(super) fn terminal_from_audit'
        original=data.decode().split(marker)[0]
        assert hashlib.sha256(original.encode()).hexdigest()==expected
        expected=meta['compact_verifier_files'][name]
    assert hashlib.sha256(data).hexdigest()==expected
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
name='r17_compact_ordinary.rs';path=root/name
old=path.read_text()
wrapper=old[old.index('\n#[inline(never)]\npub(super) fn terminal_from_audit'):]
path.write_text(Path(__file__).with_name(name).read_text()+wrapper)
meta['compact_storage']={name:{'before_sha256':meta['compact_verifier_files'][name],
    'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}}
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
# Refresh exact pins for the now-integrated callback and storage candidate.
# Every inherited source change is also checked by the SBF transformation chain.
for name in control['files']:
    control['files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
control['scope']='compact ordinary storage fix after oversized SBF constructor; focused source gate'
(a.output/'r17-compact-control.json').write_text(json.dumps(control,indent=2)+'\n')
