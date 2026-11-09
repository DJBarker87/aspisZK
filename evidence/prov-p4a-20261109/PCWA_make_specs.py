#!/usr/bin/env python3
"""PCWA_make_specs.py RUN KEY : write <RUN>_spec.json for one reference-crate extraction from PCWA_SOURCES.json.
Argument shape = the original receipts' (NDL_extract.py / slice-d *-extraction-pins.json): core includes, --start-from roots,
cargo '--offline --release --lib --jobs 1', Aeneas '-sequential -no-progress-bar -abort-on-error -backend lean -split-files'.
Only host paths and the emission directory change."""
import json,sys,os
from pathlib import Path
E=Path(__file__).resolve().parent
HOST=os.environ.get('PCWA_HOST_BASE','/home/dombarker/project-offloads/codex-pc-prov-p4a-20261109')
TOOL='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin'
TOOLSHA={'charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','aeneas-b59d5188-extended':'c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'}
CONF={
 'NGM_GuardRef':dict(ns='NDL_GuardRef',roots=['qeq_ref','roweq_ref','guard_raw_ref'],covers=['NGM_GuardRef.Funs','NGM_GuardRef.Types'],orig=None,
    orig_receipt='evidence/native-front1b-20261028/NDL_E004/receipt.json'),
 'NGD_AtG':dict(ns='NGD_AtG',roots=['parse_at_g'],covers=['NGD_AtG.Types','NGD_AtG.Funs'],orig={'NGD_AtG/Types.lean':'0c6e46025d5933fb0782039177848c4e73487e2b5e7f6638085234b78e5d5bf2','NGD_AtG/Funs.lean':'2e52b0a26e2db612fbcf8efee09115b1cd509fb62cf164991e44c3423ae1f5d9'},
    orig_receipt='evidence/slice-d-parser-20261104/NGD_E002-extraction-pins.json'),
 'NHJ_SnapshotReference':dict(ns='NHJ_SnapshotReference',roots=['snapshot_ref'],covers=['NHJ_SnapshotReference.Types','NHJ_SnapshotReference.Funs'],
    orig={'NHJ_SnapshotReference/Types.lean':'5eeecc95471cd483cb79d6f886953005bbce2b156edcce3d204d1f320b516042','NHJ_SnapshotReference/Funs.lean':'0feeabc55e3d27a5172ced87911f3a5d5bbbf0827c39793dbdcb4859bdbfcb6e'},
    orig_receipt='evidence/slice-d-entry3-20261106/NHJ_E001-extraction-pins.json'),
 'NHI_FilledRef':dict(ns='NHI_FilledRef',roots=['filled_ref'],covers=['NHI_FilledTypes','NHI_FilledExtracted'],
    orig={'NHI_FilledRef/Types.lean':'02107a6c8b0cdbc0df057aa61d0220dbd22ea8cf14cd392cde3837d5a6606fb8','NHI_FilledRef/Funs.lean':'658ff2aeee028f97514a6267a9707e60598a909ffe6ef3f8bc4cdd18239e02b9'},
    orig_receipt='evidence/slice-d-pair-20261106/NHI_E001-extraction-pins.json'),
 'NHE_TensorRef':dict(ns='NHE_TensorRef',roots=['tensor_ref'],covers=['NHI_TensorExtracted'],
    orig={'NHE_TensorRef/Types.lean':'31add0cd8087c13d5d1d25ab6514d7e044c0cf8487067d01e1d87af721f3a40e','NHE_TensorRef/Funs.lean':'aa373dc158a20e16c81ba0f090757c8e4186a32d03b9b1e15a9eaebac28b117e'},
    orig_receipt='evidence/slice-d-finish3-20261106/NHE_E001-extraction-pins.json'),
 'NHE_GroupRef':dict(ns='NHE_GroupRef',roots=['group_ref'],covers=['NHI_GroupExtracted'],
    orig={'NHE_GroupRef/Types.lean':'d41decde664f9e3d17ca0c1a2c8fe39b588ce6b0e27d1b068ef05871fc1e3ce3','NHE_GroupRef/Funs.lean':'3ed15d52fd9da1c71584f3e70e595a641be77b530de68bbd4c83fe8e471f9f3a'},
    orig_receipt='evidence/slice-d-finish3-20261106/NHE_E002-extraction-pins.json'),
}
def main(run,key):
    c=CONF[key];src={s['id']:s for s in json.loads((E/'PCWA_SOURCES.json').read_text())}[key]
    out=f'{HOST}/{run}_emitted';crate=f'{HOST}/{run}_crate'
    ch=[f'{TOOL}/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
    for r in c['roots']:ch+=['--start-from','crate::'+r]
    ch+=['--dest-file',f'{out}/repro.llbc','--','--manifest-path',f'{crate}/Cargo.toml','--offline','--release','--lib','--jobs','1']
    ae=[f'{TOOL}/aeneas-b59d5188-extended','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',c['ns'],'-dest',f'{out}/raw','-subdir',c['ns'],'-split-files',f'{out}/repro.llbc']
    up={f'sources/{key}/Cargo.toml':f'sources/{key}/Cargo.toml',f'sources/{key}/src/lib.rs':f'sources/{key}/src/lib.rs'}
    spec=dict(run=run,label=key,covers=c['covers'],charon_command=ch,aeneas_command=ae,tool_sha256=TOOLSHA,
      crate_files={'Cargo.toml':dict(upload=f'sources/{key}/Cargo.toml',sha256=src['manifest_sha256']),'src/lib.rs':dict(upload=f'sources/{key}/src/lib.rs',sha256=src['src_sha256'])},
      upload=up,target_dir=f'{run}_target',original_outputs=c['orig'],original_receipt=c['orig_receipt'],source_provenance=src,
      expected_limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'})
    (E/f'{run}_spec.json').write_text(json.dumps(spec,indent=1)+'\n');print(run+'_spec.json')
main(sys.argv[1],sys.argv[2])
