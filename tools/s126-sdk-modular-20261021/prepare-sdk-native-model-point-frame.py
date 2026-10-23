#!/usr/bin/env python3
"""Candidate native point frame using real guard models with checked unary specs.
NOT accepted method transport: complete common-spec uniqueness, ABI/state
adequacy and exact source pins must be discharged before ordinary stubs count.
"""
from pathlib import Path
import subprocess,sys,json,hashlib,runpy
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-point-frame.py'),str(out)],check=True)
p=out/'src/lib.rs';s=p.read_text().replace('#[cfg(kani)] mod proofs {','mod sdk_live_models;\n#[cfg(kani)] mod proofs {')
needle='#[kani::proof] #[kani::unwind(48)]';assert s.count(needle)==1
associated='associated' in sys.argv[2:]
s=s.replace(needle,needle+'\n'+''.join('#[kani::stub(AccountInfo::'+method+',crate::sdk_live_models::'+('Models::' if associated else '')+mode+')]\n' for method,mode in [('try_data_len','length'),('try_borrow_data','shared'),('try_borrow_mut_data','exclusive')]))
p.write_text(s);model=R/'tools/s126-sdk-modular-20261021/sdk-live-models.rs';model_text=model.read_text()
if associated:model_text=runpy.run_path(str(R/'tools/s126-sdk-modular-20261021/make-associated-sdk-model.py'))['associated'](model_text)
(out/'src/sdk_live_models.rs').write_text(model_text)
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),sdk_model_source_sha256=hashlib.sha256(model_text.encode()).hexdigest(),qualification=__doc__,remaining='Both actual and unassociated-model unary complete-spec checks pass separately. Associated-model contracts, unique outcome/complete heap+ABI adequacy proof and enclosing transport remain required. Native point check codegen or passing properties alone does not certify these ordinary stubs. Decoder cut/pure scan/actual successful child/runtime/oracle transport still required.')
p.write_text(json.dumps(m,indent=2)+'\n')
