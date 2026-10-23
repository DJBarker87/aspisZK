#!/usr/bin/env python3
"""EXCLUDED experiment: ordinary real-guard SDK model stubs in native caller.
The required external equivalence certificates have NOT passed. Generation
and codegen confer no correspondence credit; do not use this as evidence.
"""
from pathlib import Path
import json,hashlib,subprocess,sys
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-shared-prefix.py'),str(out),'unreachable-cuts','exact-vec'],check=True)
p=out/'src/lib.rs';s=p.read_text();needle='#[cfg(kani)] mod proofs {'
assert s.count(needle)==1;s=s.replace(needle,'mod sdk_live_models;\n'+needle)
needle='#[kani::proof_for_contract(native_prefix)] #[kani::unwind(48)]'
assert s.count(needle)==1
stubs=''.join('#[kani::stub(AccountInfo::'+method+',crate::sdk_live_models::'+name+')]\n' for method,name in [('try_data_len','length'),('try_borrow_data','shared'),('try_borrow_mut_data','exclusive')])
s=s.replace(needle,needle+'\n'+stubs);p.write_text(s)
model=R/'tools/s126-sdk-modular-20261021/sdk-live-models.rs';(out/'src/sdk_live_models.rs').write_bytes(model.read_bytes())
p=out/'source-cut.json';meta=json.loads(p.read_text());meta.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),sdk_live_model_sha256=hashlib.sha256(model.read_bytes()).hexdigest(),sdk_method_transport='Actual registry SDK2.3.0 remains selected; all three original method calls have exact real-guard/status/counter/frame references. These ordinary stubs require pinned standalone source-equivalence certificates for each method plus the native parent proof. No Arbitrary impl, alternate guard type or SDK source patch is used. The original native stage1 source and complete borrowed reference remain intact.')
p.write_text(json.dumps(meta,indent=2)+'\n')
