# LPm installed stubs

| Replacement | Target | Domain | Paired Lean theorem | Native stage |
|---|---|---|---|---|
| LPi_contracts::qbytes (unchanged inherited bytes) | QM31::write_le_bytes | Every four raw U32 limbs; exact 16-byte mutable slice | AspisR1.LPi_WriterValues.qm_writer (LPm_L001 unchanged dependency replay) | LPm_K003 PASS; LPm_K002 timeout (excluded) |

The replacement chooses nondeterministic bytes and constrains every byte to the natural little-endian words. It asserts passed slice length 16. Native put_k allocates that exact buffer. Checkpoint stages install no field multiplication replacement. The inherited module contains unused definitions; their presence is not claimed as native evidence. LPi_STUBS.md retains every inherited pairing and its qualification.

## Prepared continuing-call replacement

`verifier::LPm_verifier::LPm_emul::replacement` targets `WideExact::mul`.
Domain: every eight canonical natural limbs in each native private E value.
Paired emitted theorem: `AspisR1.LPi_TowerValues.wide_mul` (unchanged dependency
replay L030): total success, canonical result, `ew out = mulE (ew a) (ew b)`.
The replacement chooses `kani::any()` canonical limbs and assumes that EXACT
natural formula. Its wrapping reference instructions do not change the formula:
LPm_StubBounds.product/canonical_sum/residue (L050) show all product operands fit
u32, products fit u64, additive/subtractive representatives do not overflow or
underflow, and all residue subcalls remain canonical. These are specifications
in assumptions, not field multiplications proved by Kani. The caller constructs
both inputs via the native checked private E constructor and the replacement
asserts the canonical domain. K008 is a NEW isolated continuing-call cut, with
redundant reference overflow checks removed by these bounds; it is not a replay
of LPi_K014's full-array/branch/multiply shape. K008 timed out at90s, excluded; no rerun. K009 is a separate return-threading split with the SAME full natural-value replacement, K009 PASS:117 checks, one unreachable; paired whole-value law retained.

## Native public push context

`fast_pairing::canonical::LPm_pairing::LPm_dot` replaces private `Dot::push`.
Domain: every four-u64 self state and canonical four-u32 a/b (asserted inside
the replacement, established by native from_wide / checked_q in the public
caller). Pair: `AspisR1.LPm_PublicState.private_source`, L055, total emitted
push, derived raw values EXACTLY LPi_RawValues.spec and four wrapping fold
updates. `LPm_spec` is the frozen raw formula expressed with wrapping reference
instructions; its natural-value pairing is LPi_RawValues.source, L037, under
the SAME canonical bounds. Each raw result is `kani::any()` assumed equal to
that specification. This job never proves a field product in Kani.

Additional ghost-only assertions check each actual a/b word, left/right call
order and typed pointer identity to the live caller's actual c0/c1. No typed
guard is fabricated or obtained by address-word equality. The replacement
writes only its borrowed Dot and the ghost call counter. K013 PASS: 628 checks (eight unreachable), three covers; the
full caller ABI and canonical rejection path are checked. K010 checks the real source coordinate
update independently on arbitrary u64 states/raw values, all four coordinates
and complete frame; LPf_DotPushFour and LPm_WordFold supply induction/bounds.


K015's LPm_weighted_mul targets the same WideExact::mul, calls the same
LPm_emul replacement and asserts actual selected operands before delegation.
It has the SAME L030.wide_mul domain/value pairing; K015 timed out and is
excluded. K016's weighted_add_tail has no stub and proves only the split
post-multiply tail. K017/K018 have no stubs. No unused harness declaration is
credited as a passing native stage.
