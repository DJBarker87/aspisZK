# Instruction-equivalence result — candidate 73070ddd51

Final comparison: `compare@5/comparison.json`; normalized disassembly, exact
diffs and timed call sites are retained in that directory. No source-only
identity is promoted into executable identity. Normalization changes only
resolved addresses/local branch offsets, adapter/module names, ELF GOT target
names and SIMD pool labels whose **16 loaded bytes** match. It preserves
opcodes, registers, arithmetic immediates, stack offsets and branch structure.
Anonymous metadata references remain distinct. Compare @2 failed because one
call-site output still used the old normalizer signature; @3 repaired that;
@4 added constant-pool byte comparison; @5 binds the final changed binary.
None of these static comparisons runs a kernel.

| Family | Exact comparison and difference | Attribution |
|---|---|---|
| SeedExpander m31 | Candidate has no standalone m31 symbol: it is inlined in sample_mask_cells; harness emits measure_m31 | Harness only; no symbol equivalence asserted |
| SeedExpander qm31 | 258 instructions each; domain/metadata references differ, plus actual rax/rdx and cl/al return-store register allocation in the success/exhaustion return-store blocks (exact sequences in mask-qm31-0.diff) | Harness only, including synthetic rejection variant |
| Pole scan | 87 instructions each; only normalized index 72 cold panic_bounds_check metadata pointer differs; executable scan/return prefix matches | Full symbol not equal under conservative normalization; valid-shape prefix only matches |
| M31::inv | 514 instructions each; only indices 503–504 cold panic_fmt message/location pointers differ | Full symbol not equal; nonzero arithmetic/return prefix matches |
| QM31 norm path | QM31::try_inv, 308 instructions, normalized equality | Matching leaf reached by harness inverse_q → QM31::inv → try_inv; interval also includes harness wrapper/Option check and M31::inv callee |
| Tagged compressor | compress_tagged_tuple, 350 instructions, normalized equality, including loaded vector constants | Harness main directly calls this equal body; candidate copy_endpoint_values also calls its equal body; full intervals/callers still differ |
| Private seed checks | Candidate entropy_nonzero32 is inlined in generate_for_mask_nonce; harness has a ten-instruction SIMD predicate plus padding in seed_check | Harness predicate only; no equivalence of generate_for_mask_nonce's full check composition, OS fill or retries |

Every measured interval will speak directly for the retained `pv-dudect`
executable. The matched compressor/try_inv leaves support the narrower
instruction-binding claim above. The task does not establish full candidate
binary timing equivalence. No timing result has been obtained.


mask-m31 symbol locations:

- harness: `pv_dudect::kernels::state_only_hiding::measure_m31 @ 0x37700`
- candidate: `aspis_prover::state_only_hiding::sample_mask_cells @ 0x13bee0`

mask-qm31 symbol locations:

- harness: `pv_dudect::kernels::state_only_hiding::measure_qm31 @ 0x37850`
- candidate: `aspis_prover::state_only_hiding::SeedExpander::qm31 @ 0x13b8a0`

pole symbol locations:

- harness: `pv_dudect::kernels::ct_pole::all_slots_clear @ 0x37f10`
- candidate: `aspis_r1_cost_probe::ct_pole::all_slots_clear @ 0xc74e0`

m31-inv symbol locations:

- harness: `pv_dudect::inverse_m @ 0x33460`
- harness: `aspis_core::field::M31::inv @ 0x42cf0`
- candidate: `aspis_core::field::M31::inv @ 0x19d8c0`

qm31-inv symbol locations:

- harness: `pv_dudect::inverse_q @ 0x33470`
- harness: `aspis_core::field::QM31::inv @ 0x43570`
- harness: `aspis_core::field::QM31::try_inv @ 0x435c0`
- candidate: `aspis_core::field::QM31::try_inv @ 0x19ec00`

compress symbol locations:

- harness: `pv_dudect::kernels::prover_shared::compress_tagged_tuple @ 0x36b30`
- candidate: `aspis_r1_cost_probe::host_semantic::copy_endpoint_values @ 0xb8ff0`
- candidate: `aspis_r1_cost_probe::prover_shared::compress_tagged_tuple @ 0xbe590`

seed-checks symbol locations:

- harness: `pv_dudect::kernels::entropy::seed_check @ 0x38070`
- candidate: `aspis_prover::state_only_entropy::StateOnlyAttemptSecrets::generate_for_mask_nonce @ 0x140560`

Binary SHA256 pins:

- `pv-dudect`: `ede68055604cce057f3d0b96fa575b06f30290bba4bcdb50493b7b81a797eb02`
- `devnet_spend`: `161abfd8d155a2ccf35a461cd8e03fbf909e0f8b1c59efdddec1d76e74811472`
