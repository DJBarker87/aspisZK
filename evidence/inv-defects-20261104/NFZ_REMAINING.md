# NFZ remaining obligations after part 3

**INCOMPLETE — mandatory STOP after NFZ_B005 own-script failure. NFZ_B006 unused.** The last allocation was two scopes; one was spent. The explicit conditional stop overrides whole-budget use and the usual own-script repair-and-continue rule. No further launch in this job.

B005 passed local payload validation and byte-identical dry collection of all495 files before admission. The library emitted stable MIR; the program build failed when libc's build script called the wrapper for a rustc probe. Cargo strips RUSTFLAGS in this environment; NFZ_rustc.py:7 raised `KeyError: 'RUSTFLAGS'`. Cargo program exit101 propagated to scope exit1. Full exact failure: NFZ_B005/stdout.log and NFZ_B005_FAILURE.md. Measured peak17 threads;25.118775121169165s;751856KiB;swap0. Frozen source/lock stayed unchanged.

## Corrected command, recorded only

The wrapper must restore the flags it requires before checking them, including when called by a build-script version probe. Replace the failed environment lookup with this proposed code (retain affinity and one-job checks):

```python
flags = os.environ.get('RUSTFLAGS', '-C codegen-units=1')
assert '-C codegen-units=1' in flags
os.environ['RUSTFLAGS'] = flags
# Cargo passes encoded flags to actual compilation; a nested build-script
# probe can omit them. Enforce the bound at the rustc command as well.
args += ['-C', 'codegen-units=1']
```

No wrapper replacement or compiler rerun was performed after the failure. If the lead commissions another job, its corrected program command inside its admitted one-CPU/one-token monitored scope is:

```sh
set -euo pipefail
export CARGO_BUILD_JOBS=1 CARGO_NET_OFFLINE=true CARGO_INCREMENTAL=0
export RUSTFLAGS='-C codegen-units=1'
export RUSTC_WRAPPER=/home/dombarker/project-offloads/codex-cx-inv-defects-20261104/NFZ_rustc.py
/home/dombarker/.cargo/bin/cargo +1.94.1 rustc \
  --manifest-path /home/dombarker/project-offloads/codex-cx-inv-defects-20261104/NFZ_src/programs/r1-cost-probe/Cargo.toml \
  -p aspis-r1-cost-probe-program --locked --offline \
  --features pool-adapter,private-leaf-salts --lib -j1 \
  --target-dir /home/dombarker/project-offloads/codex-cx-inv-defects-20261104/NFZ_target \
  -- --emit=mir -C codegen-units=1
```

This is not permission to run it. Payload preflight/dry collection, source/lock pins, one-slot jobserver and admission remain prerequisites. B005 must never be resubmitted. Its own scratch target was removed after recovery; retained named cache was untouched.

## Remaining members and claim boundary

Every candidate NFZ_C0001 through NFZ_C0039 remains pending entry/independent review, individually listed in NFZ_CANDIDATES.json with a part3 disposition. Six historical core body identities remain established; they do not supply complete entry reachability. C0003–C0024 are the22 Transcript::queries embeddings; C0025 is accumulate_batched_with_node; C0026–C0031 are Weights::new chains; C0032 is map(extension_limbs); C0033 is first_decoded→error; C0034 is the source-cfg-disabled legacy callback; C0002 is the sampler fallback; C0001/C0035–C0039 are embedding-chain sites. No classification was silently promoted from source discovery.

TX2:046 and TX2:211 remain OPEN, outside slice membership; neither is REACHABILITY-EXCLUDED. Pending: complete two-caller compiler authority, independent authority,39-candidate review, new OPEN TX occurrences for reached missing functions (including transitive callees), reviewed pinned overlay, and regenerated repaired closures/counts. Baseline closure regeneration still yields585/587, zero admitted edges/new rows/status changes/CLOSED promotions. See NFZ_LEDGER_DELTA.json.

The prospective Q caller finding remains unadmitted. NFS_NEV_AccumPacket.result_state_effects covers the complete modeled accumulation; NFS_NEV_AccumulateCallees.from_m31 explicitly identifies canonical embedding. NFM dot packets do not cover this embedding or Transcript::queries. Report confirmed edges to the lead against the caller Q row without changing its status; current partial evidence is not that completed report.

Kani0/0, extraction0/0, Lean0/5. Each remaining member needs rustc entry/independent evidence or its reviewed inventory consequences; no Lean theorem or Lean-importing validator can supply that evidence. No theorem added; #print axioms N/A. Early stop at1/2 scopes is expressly required by the lead's conditional rule, not discretionary budget saving. D188/L187 and the100-bit per-attempt target remain unestablished by this job.
