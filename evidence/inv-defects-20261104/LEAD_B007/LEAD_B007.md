# LEAD_B007: statement-crate MIR for the residual candidate NFZ_C0032 (lead-run, 2026-11-04)

- Admission: JFz_reservation.py exit 0, allowed:true (admission.json, barrier.log). Scope: systemd-run --user --scope
  MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64 (run.sh). Attempt 1 failed in 0.03 s because the crate has
  no pool-adapter/private-leaf-salts features (stderr.attempt1.log); attempt 2 ran without the flag.
- Command: cargo +1.94.1 rustc --manifest-path NFZ_src/programs/r1-cost-probe/Cargo.toml -p aspis-statement --locked
  --offline --lib -j1 -- --emit=mir -C codegen-units=1; CARGO_BUILD_JOBS=1, no RUSTC_WRAPPER; host target, MIR only.
- Cargo.lock sha256 before/after 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef (unchanged).
- Exit 0; wall 12.40 s; max RSS 736,552 KiB; swaps 0. #print axioms N/A.
- Output aspis_statement.mir.xz sha256 088be272223412063fd2f6328c8d0f58ebc14a6e274ec957117072e5bd164b72.

## Finding
`external_local_packed_raw` (MIR line 247684) calls
`array::<impl [QM31; 4]>::map::<fn(QM31) -> [u32; 4] {state_only_poseidon::extension_limbs}, [u32; 4]>(_, extension_limbs)`
(offset line 227 inside the body). The callback edge external_local_packed_raw -> state_only_poseidon::extension_limbs
is compiler-confirmed; the callee already has row TX1:310. extension_limbs is also referenced from
external_linear_lazy (lines 246917-247525). The edge is to be admitted through the NGB_ overlay/producer by the next
inventory or ledger job (NFZ_C0032 -> ADMITTED), not by hand. No other change.
