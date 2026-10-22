#!/usr/bin/env python3
"""Direct actual-SDK/real-guard-model coupling, with frame checked separately.
Only one SDK operation is paired. Ordinary proof avoids re-instrumenting the
already checked unary counter-only DFCC frames across the two executions.
No SDK function is stubbed; both return actual std guard/ProgramError types.
"""
from pathlib import Path
import sys,json,hashlib,runpy
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-live-contracts/sources'
out=Path(sys.argv[1]);mode=sys.argv[2];assert mode in ['length','shared','exclusive'];assert not out.exists()
base=E/('sdk-live-model-length-v2' if mode=='length' else 'sdk-live-model-'+mode+'-v1')
(out/'src').mkdir(parents=True)
s=(base/'src/lib.rs').read_text()
a=s.index('#[kani::requires(');b=s.index('fn compare_live(',a);s=s[:a]+s[b:]
needle='#[kani::proof_for_contract(compare_live)]';assert s.count(needle)==1;s=s.replace(needle,'#[kani::proof]')
s=s.replace('sdk_live_models::'+mode+'(account)','sdk_live_models::Models::'+mode+'(account)')
s=s.replace('assert_eq!(*error,ProgramError::AccountBorrowFailed)','assert!(matches!(error,ProgramError::AccountBorrowFailed))')
s=s.replace('assert_eq!(error,ProgramError::AccountBorrowFailed)','assert!(matches!(error,ProgramError::AccountBorrowFailed))')
assert '[u8;10485760]' in s and 'length<=10485760' in s
assert '#[kani::stub' not in s and '#[kani::modifies' not in s
model=(R/'tools/s126-sdk-modular-20261021/sdk-live-models.rs').read_text()
model=runpy.run_path(str(R/'tools/s126-sdk-modular-20261021/make-associated-sdk-model.py'))['associated'](model)
(out/'src/lib.rs').write_text(s);(out/'src/sdk_live_models.rs').write_text(model)
c=(base/'Cargo.toml').read_text();c=c.replace('name="aspis-s126-sdk-live-model-join"','name="aspis-s126-sdk-live-pair-'+mode+'-v1"')
assert 'name="aspis-s126-sdk-live-pair-'+mode+'-v1"' in c
(out/'Cargo.toml').write_text(c)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',mode=mode,source_sha256=sha(out/'src/lib.rs'),model_sha256=sha(out/'src/sdk_live_models.rs'),base_source_sha256=sha(base/'src/lib.rs'),qualification=__doc__,domain='Same full one-account typed host heap as original contracts: 10MiB storage/all view lengths, arbitrary bytes/metadata, every signed data/lamport count and every nonzero usize Rc header. Exact original SDK and associated real-guard models both execute; real guards dropped between executions and afterward. All enabled checks/covers required.',remaining='Ordinary pair is not a new write-frame certificate: compose the previously verified native/model unary counter-only frames at matching source/ABI pins. General runtime fixture embedding, actual caller/refinement and source child/oracle installation remain separate. No whole S2 closure.'),indent=2)+'\n')
