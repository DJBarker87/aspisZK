# Reused Dot raw stub pairing

No new translated field-multiplication stub is introduced. The six field stub
pairings remain exactly [LPh_STUBS.md](../leaf-p6-8-20261027/LPh_STUBS.md).
The native Dot four-coordinate consumers LPh_K004–K007 are reused with their
per-run frozen graph/unchanged-lock validation in LPh_VERIFICATION.json; no
LPb or drifted dependency stage is consumed.

| Reused stub | Named paired Lean theorem | Domain established by caller |
|---|---|---|
| canonical::LPh_dot::raw_stub, including observational LPh_RAW | AspisR1.LPn.Raw.raw_nat (L073), AspisR1.LPn_RawReference.source (L072), LPn.Dot.raw_same (L075), final LPn.Dot.native_result (L080) | Stub asserts all eight packed U32 words<P. K013 proves exact checked_q/from_limbs rejection/packing and validated WideExact::from_wide packing/canonicality. Actual Dot callers are EbyKDot::push (checked scalar, private validated E) and EDot::push (two private validated E values). Existing WideExact constructor/operation invariant is retained; no new input-canonicality assumption is added. |

The stub returns any array constrained to the exact wrapping natural raw spec,
then records THAT SAME returned array in its ghost. L073 proves the emitted
operation returns ok with precisely that Nat list; L075 jointly identifies
it with the SAME-word cohort raw list in the repaired import context. L080
DERIVES the raw call/result rather than assuming it. L079 supplies the exact
U64 wrapping-state port. Ghost recording is observational only; it does not
alter a returned word or the shipped source. No native multiplication proof
or new blanket compiler/library/field trust item is used.
