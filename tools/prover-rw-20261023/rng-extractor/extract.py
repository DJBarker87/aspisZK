"""Bounded optimized Charon invocation; translating the actual source is separate.

Both Charon and Aeneas count against the 12-invocation operational budget.
This script must itself run through the existing independently capped launcher.
"""
from pathlib import Path
import os, subprocess, sys
R=Path(__file__).resolve().parents[3]
D=Path(__file__).resolve().parent
kind=sys.argv[1]
assert kind in ['synthetic', 'selected64']
charon='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default']
if kind=='synthetic':
    for name in ['crate::wrap','crate::selected','crate::move_value','crate::copy_error','crate::repeated']:
        cmd+=['--start-from',name]
    includes=['getrandom::error::Error','core::num::nonzero::NonZero','core::num::niche_types::NonZeroI32Inner','core::result::_::map_err']
    manifest=D/'synthetic/Cargo.toml'
    extra=[]
else:
    cmd+=['--opaque','crate','--opaque','aspis_prover','--opaque','aspis_core','--opaque','aspis_statement',
          '--start-from','crate::RealR1_client::prove_for_proof_accounts']
    includes=['crate::RealR1_client::prove_for_proof_accounts','crate::prover::prove_masked_retrying_with',
        'crate::prover::RetriedProof','crate::prover::MaskedFixtureAudit',
        'crate::transport::Variant','crate::verifier::Error',
        'aspis_prover::state_only_entropy::_::generate_for_mask_nonce',
        'aspis_prover::state_only_entropy::entropy_nonzero32',
        'aspis_prover::state_only_entropy::StateOnlyAttemptSecrets',
        'aspis_prover::state_only_entropy::StateOnlyAttemptEntropyError',
        'aspis_prover::state_only_entropy::_::from',
        'getrandom::error::Error','core::num::nonzero::NonZero',
        'core::num::niche_types::NonZeroI32Inner','zeroize::Zeroizing',
        'core::result::_::map_err']
    manifest=R/'crates/aspis-r1-cost-probe/Cargo.toml'
    extra=['--features','optimized-terminal,ct-host-prover']
for name in includes:
    cmd+=['--include',name]
cmd+=['--dest-file',str(D/('ProverRwRngExtractor'+kind+'.llbc')),'--',
      '--manifest-path',str(manifest),*extra,'--offline','--release','--lib','--jobs','4']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-06-01',
    CARGO_TARGET_DIR=str(R.parent/'rng-charon-target'))
raise SystemExit(subprocess.run(cmd,cwd=R,env=env).returncode)
