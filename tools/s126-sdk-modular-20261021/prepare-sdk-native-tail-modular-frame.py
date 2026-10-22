#!/usr/bin/env python3
"""Post-first source frame with directly coupled actual-guard SDK rewrites.
No return/account carrier is simplified. Each replacement must be justified by
original/model unary full-heap frames, ordinary direct whole-guard-word/result
coupling and actual Drop frames at matching source/tool/ABI pins. This helper
is not by itself the concrete contextual SDK rewrite certificate.
"""
from pathlib import Path
import subprocess,sys,runpy,json,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-tail-write-frame.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();s=s.replace('use aspis_r1_cost_probe::','mod sdk_live_models;\nuse aspis_r1_cost_probe::',1)
needle='#[kani::stub_verified(encoded_finish)]';assert s.count(needle)==1
s=s.replace(needle,needle+'\n#[kani::stub(AccountInfo::try_borrow_data,crate::sdk_live_models::Models::shared)]\n#[kani::stub(AccountInfo::try_borrow_mut_data,crate::sdk_live_models::Models::exclusive)]')
p.write_text(s)
model=runpy.run_path(str(R/'tools/s126-sdk-modular-20261021/make-associated-sdk-model.py'))['associated']((R/'tools/s126-sdk-modular-20261021/sdk-live-models.rs').read_text())
(O/'src/sdk_live_models.rs').write_text(model)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s126-sdk-native-tail-write-frame-v3','aspis-s126-sdk-native-tail-modular-frame-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),model_sha256=hashlib.sha256(model.encode()).hexdigest(),qualification=__doc__,remaining='All properties/covers must pass. Source-specific SDK rewrite consumes direct coupling+unary heap frames+same typed/provenance/layout/Drop and no observable SDK internal effects; explicit proof/audit required. Source finish-owner and entry/post-first source composition plus actual child/scan/gate/runtime/oracle/TX2 remain. No whole S2 claim.'),indent=2)+'\n')
