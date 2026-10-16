Result.ok decoder attempt7269c3a39, retained2026-10-16

Status: NOT extraction-closed; source excluded from reviewed integration.
The40 guarded fixed conversions now use Result.ok then Option.unwrap; the8
indexed digest conversions are unchanged. Source review confirmed all40 exact
insertions and restored the preceding72a files modulo whitespace after reversal.
Whole-input length rejection and all field/header/error ordering are unchanged.

Charon passed72.258s,654348KiB process RSS,660201472B cgroup peak.
Aeneas failed2 after2.503s,255316KiB RSS,242823168B cgroup peak:
“There should be no bottoms in the value”, core/src/result.rs713–717,
InterpExpressions.ml55. Actual std Result.ok was included, not modeled.
LLBC moves the Ok payload, then a drop-cleanup switch rereads partially moved
self. No generated output or Lean closure is claimed. No unchanged retry.

Native optimized build passed67.165s,548252KiB; trace passed0.154s,1936KiB.
The full20,720-case66,622,110-byte output agrees with the retained42e5 baseline.
Hash-counter regression passed52.481s,545180KiB (exact time.log retained).
Native/extraction scopes6/8GiB; counter8/10GiB; all swap zero.
No SBF/CU rerun was made for this rejected extraction candidate.

Replacement0626294e3 introduces one source-owned helper whose Result payloads
are Copy and whose failure is a literal panic, avoiding generic-drop cleanup.
That candidate needs its own extraction, actual-function audits and regressions.
No external or compiler axiom is admitted by this attempt.
