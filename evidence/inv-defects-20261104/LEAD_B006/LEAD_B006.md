# LEAD_B006: compiler evidence for the inventory defects (lead-run, 2026-11-04)

After NFZ_ parts 1-3 lost four host scopes to its own tooling, the lead ran the one missing compiler step
directly. This file records the evidence; the inventory repair itself is NOT applied here (job NGB_).

## Run
- Host admission: JFz_reservation.py exit 0, allowed:true (admission.json, barrier.log).
- Scope: systemd-run --user --scope MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64 (run.sh).
- Command: cargo +1.94.1 rustc --manifest-path NFZ_src/programs/r1-cost-probe/Cargo.toml
  -p aspis-r1-cost-probe-program --locked --offline --features pool-adapter,private-leaf-salts --lib -j1
  -- --emit=mir -C codegen-units=1; CARGO_BUILD_JOBS=1, no RUSTC_WRAPPER. Host target (MIR only, no SBF).
- Source tree: NFZ_src staged by NFZ_ (byte-validated against the frozen revision 4bb3b3f5…, NFZ_PAYLOAD_PREFLIGHT.json).
- Cargo.lock sha256 before and after: 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef (unchanged).
- Exit 0; wall 1:06.33; max RSS 754,704 KiB; swaps 0 (stderr.log). #print axioms: N/A (no Lean).
- Output: aspis_r1_cost_probe_program.mir.xz, sha256 f93b0dfd49aa4a67cf2883c299ec72527ca7f33f0b5040f4ae4297121db77163
  (uncompressed sha256 c9bebf9eb6f708bc4c4d9de7533d578eddc536b1152fac8404bd1bcb2ac01cff, 19,324 lines).

## Findings (stable rustc 1.94.1 MIR, deployed feature set, no `prover`)
1. TX2:211 / lib.rs::error. Program MIR: `first_decoded` calls
   `Result::map_err::<ProgramError, fn(Error)->ProgramError {error}>(_, error)` (MIR line 337) and
   `stage2_owned` does the same (line 16973). Both callback edges are compiler-confirmed. first_decoded is on
   the TX1 path, so TX1 lacks a row for lib.rs::error as well as the edge; TX2:211 gains its incoming edge.
2. TX2:046 / scalar.rs::WideExact::from_m31. Library MIR from NFZ_B005 (NFZ_B005_aspis_r1_cost_probe-….mir.xz,
   same feature set): `Transcript<H>::queries` calls `<WideExact as CodeField>::from_m31` at 22 sites
   (trace tag 5), `accumulate_batched_with_node` at 1 site (trace tag 13), `accumulate_with_node` at 1 site.
   The calls are unconditional in source (transcript.rs:56-77, verifier.rs:263, :285); trace::value is a
   no-op without `prover` but its argument is still evaluated. So the edge exists on BOTH transactions; TX1
   has no WideExact::from_m31 row at all. `accumulate`/`accumulate_with_node` have no caller in the program
   MIR (0 references) and none in the deployed crate sources outside eight_way (audit feature): candidate
   REACHABILITY-EXCLUDED, to be confirmed by the inventory producer, never silently dropped.
3. The same construction (`trace::value(_, _, E::from_qm31(..))`, tags 11/12) already has rows
   (WideExact::from_qm31 TX1:050/TX2:033), so the defect is specific to the trait-dispatched call.
4. Consequence for slice Q (lead ruling pending NGB_'s regenerated closure): accumulate_batched_with_node
   (TX1:182/TX2:108, CLOSED under NFS_) and Transcript::queries (TX1:168) have a callee their model
   packets did not name. The native certificates executed the real code, so the callee's effect (a pure
   conversion whose result is discarded) is covered natively; the model side must either name it or prove
   the discarded-argument erasure. NFS_NEV_AccumulateCallees.from_m31 reportedly identifies the canonical
   embedding; NGB_ must cite the exact statement. Until then those rows carry an OPEN callee-naming
   obligation but are not downgraded.
