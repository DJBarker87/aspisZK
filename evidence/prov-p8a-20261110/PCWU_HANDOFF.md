# PCWU_ (P8a) translator lane round 1: handoff

FIRST, a non-encoding modelling difference (no gate involved): under TV3 the frozen stage1 adapter extracts (PCWU_E003, exit 0), but the emitted model drops the checkpoint write `accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint)` (r1_pool_adapter_owned.rs:457). The write goes through RefCell interior mutability behind `&AccountInfo`, and Aeneas gives try_borrow_mut_data Unit-valued backward functions. This affects every input that reaches line 457. See PCWU_ANALYSIS_1.md. The emission is not credited and must not discharge TX1:344.

Limitation (1), guard drop (InterpBorrows.ml:2731): not reproduced on any frozen root and not patched. Under the original pair, Dot::push (E001) and snapshot (E002) translate, and stage1/stage2 fail at Interp.ml:609 (type parameters containing mutable borrows). Under TV3 all three adapters translate (E003). The cause is analysed from source in PCWU_ANALYSIS_1.md.
Credit from the Dot::push emission (original pair, ON), PRVEq_PCWU_AspisR1DotPushLocal.lean, compiled in PCWU_L002 (exit 0, standard axioms only):
- AspisR1DotPushLocal.Types: Q and Dot are EQUALITY_PROVED.
- AspisR1DotPushLocal.Funs: P is EQUALITY_PROVED.
- Dot.push is CONDITIONAL_ON_BINDING (rawFn := Q::raw). The frozen 0..4 loop is proved equal to the gate's four literal steps.
PCWU_L001 failed on an unreduced `uncurry`; the shape was changed for L002.

Limitation (2), nested-loop returns: reproduced on prepared_claim (E004, TV3). The fix is designed in PCWU_ANALYSIS_2.md (an Option-typed exit local per loop level, plausibly upstreamable) but not built. No TV4 exists.

Scopes (all 3G/4G for extraction and 6G/8G for Lean, swap 0, admitted): E001 47 s, 694 MB; E002 70 s; E003 57 s; E004 32 s; L001 2.4 s; L002 2.3 s, 2.6 GB. Swap 0 throughout. Budget used: 4/16 extraction, 2/16 Lean, 0 tool-build.
Files: PCWU_STATUS.json, PCWU_REMAINING.json, PCWU_CANNOT_EXTRACT.json, PCWU_CLASSIFICATIONS.json, PCWU_TOOLS.json, PCWU_ATTEMPTS.jsonl, PCWU_NEXT.md, PCWU_PATCHES/README.md.

Target not yet established
