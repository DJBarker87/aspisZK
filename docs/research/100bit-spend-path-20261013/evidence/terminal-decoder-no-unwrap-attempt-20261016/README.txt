Guarded-result decoder attempt b330ade02, retained 2026-10-16

Status: NOT extraction-closed; excluded from the reviewed integration checkpoint.
Compared with72a288c2, eight fixed digest conversions use indexed byte arrays;
40 fixed-slice conversions use map_err(WrongLength)? instead of Result.unwrap.
An independent source review checked all48 widths, guards and error priority.
This review and the finite corpus are not a universal source-refinement proof.

Charon passed (73.444s,658376KiB process RSS,679206912B cgroup peak).
Aeneas was stopped deliberately with SIGTERM after236.345s without an emitted
target (exit143,6424000KiB RSS,6572646400B cgroup peak). The6/8GiB scope had
189340 high events, no max/OOM events, and zero swaps. No larger-cap retry.
The added early-return branches are the suspected cause, not a proved diagnosis.
Operator rationale, exact command, source pins and private geometry tool hash
are retained. Four constructor renames invert to the complete original LLBC.

Optimized native build69.190s,548024KiB; trace0.158s,1760KiB;20,720 cases
match all66,622,110 output bytes against42e5ca201 (same retained trace hash).
Saved-proof counter passed53.474s,544152KiB. SBF passed42.658s,673720KiB.
One admitted-route fixture replay passed0.200s,29408KiB: stage1+1414CU,
stage2+533CU,total+1947; initial accounts, checkpoint and ASR8 bytes agree.
Existing point_claims stack diagnostics remain; no general stack-safety claim.
Rust jobs used8/10GiB scopes; native/translation6/8GiB. All swaps were zero.
No full replay; no Lean/axioms claim. Keys retained0600 on host and excluded.

Replacement7269c3a39 uses actual Result.ok then builtin Option.unwrap on the40
fixed slices, retaining the original unreachable-panic structure without Debug.
Its extraction and regression evidence are separate; this attempt stays intact.
