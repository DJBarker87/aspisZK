from pathlib import Path
import hashlib,json,difflib,subprocess
E=Path(__file__).resolve().parent;O=E.parent/'slice-d-finish-20261105'
# Retain the predecessor native snapshot verbatim. Do not rerun any passing gate.
old=json.loads((O/'NGM_NATIVE_INPUTS.json').read_text())
pins=json.loads((O/'NGM_SOURCE_PINS.json').read_text())
# Keep the already closed NGW core packet available, but do not compile/rerun it.
ours=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text())
# Use precisely the predecessor core and verifier source for its unpaired control.
(E/'NGW_PREDECESSOR_NATIVE_INPUTS.json').write_text(json.dumps(old,indent=1)+'\n')
(E/'NGW_PREDECESSOR_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
provenance={n:hashlib.sha256((O/n).read_bytes()).hexdigest() for n in ['NGM_NATIVE_INPUTS.json','NGM_SOURCE_PINS.json','NGM_K100.json','NGM_K100/receipt.json','NGM_K100/stdout.log','NGM_helper_reference.rs.txt']}
(E/'NGW_POLYNOMIAL_IMPORTS.json').write_text(json.dumps(dict(inputs=provenance,reused_pairs=[[f'NGM_K{i:03d}',f'NGM_K{i+1:03d}']for i in range(88,98,2)],control_positive='NGM_K100',new_control='same original NGM_helpers::poly_g5 name, source and feature configuration; only inversion enabled',safe_reference='NGW_E001; loop-free polynomial_step_ref; successful extraction',new_native_credit='pending matched reverse-control corruption and composed packet',no_rerun=True),indent=2)+'\n')
