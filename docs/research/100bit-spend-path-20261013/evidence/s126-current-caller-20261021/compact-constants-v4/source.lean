import CurrentCompactFirstCompositionV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentCaller.ConcreteConstants
open AspisR1CurrentCaller

/-- The seven scalar/source-constant and fixed error-mapper leaves, with all
remaining operations unchanged. Source declarations and their expression DAG
are checked against the authoritative freeze by the packet checker. -/
def withConstants (ops : Ops) : Ops :=
  { ops with
    op0 := ok {c0:={a:=0#u32,b:=0#u32},c1:={a:=0#u32,b:=0#u32}},
    op2 := fun _ => ok .Parse,
    op12 := ok 16#usize,
    op13 := ok 7015#usize,
    op14 := ok 464#usize,
    op15 := ok 13831#usize,
    op21 := ok 7527#usize }

/-- Actual checked arithmetic of the emitted constants: outer success and
exact values, independent of all data/callbacks and malformed inputs. -/
theorem constants_total (ops : Ops) :
    compact.OFF_SEMANTIC (withConstants ops)=ok 16#usize ∧
    compact.OFF_Y1 (withConstants ops)=ok 7031#usize ∧
    compact.OFF_INACTIVE (withConstants ops)=ok 7495#usize ∧
    compact.LOGICAL_Y1=ok 928#usize ∧
    compact.LOGICAL_SEMANTIC (withConstants ops)=ok 13831#usize ∧
    ((13831#usize : Usize)+(928#usize : Usize))=ok 14759#usize ∧
    compact.OFF_FOLDED_ROOT (withConstants ops)=ok 7751#usize ∧
    compact.OFF_ROUND1 (withConstants ops)=ok 7783#usize := by
  unfold compact.OFF_ROUND1 compact.OFF_FOLDED_ROOT compact.OFF_INACTIVE
    compact.OFF_Y1 compact.OFF_SEMANTIC compact.LOGICAL_Y1 compact.LOGICAL_SEMANTIC
  simp only [withConstants,bind_tc_ok]
  constructor
  · rfl
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · rfl
  constructor
  · decide
  constructor <;> decide

theorem zero_total (ops : Ops) :
    aspis_core.field.wide_exact.WideExact.ZERO (withConstants ops)=
      ok {c0:={c0:={a:=0#u32,b:=0#u32},c1:={a:=0#u32,b:=0#u32}},
          c1:={c0:={a:=0#u32,b:=0#u32},c1:={a:=0#u32,b:=0#u32}}} := by
  unfold aspis_core.field.wide_exact.WideExact.ZERO
  rfl

/-- No length/canonicality input assumption: these are constant range facts,
not totality of expansion, parsing, semantic verification or tx1. -/
theorem source_ranges :
    16≤7031 ∧ 7031≤7495 ∧ 7495≤57607 ∧
    7751≤7783 ∧ 7783≤57607 ∧ 7783-7751=32 ∧
    13831≤14759 ∧ 14759-13831=928 ∧
    14759<4294967296 := by decide

/-- Enclosing current first theorem with these source leaves installed;
there are no free numeric-offset, zero or codec-error callbacks at this root. -/
theorem first_with_constants {E : Type} (invalidAccountData : E)
    (ops : Ops) (D : aspis_core.digest.Digest32 Unit) (error : verifier.Error → Result E)
    (bytes proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : FirstComposition.firstCurrent invalidAccountData (withConstants ops) D error
      bytes proof k=ok (.Ok out)) :
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (prepared : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (semantic y1 : Slice U8) (v : verifier.View) (sem : r1_semantic.Verified Unit),
        ops.op5 proof semantic y1=ok (.Ok v) ∧
        ops.op9 D (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
          v.semantic () none=ok (.Ok sem) ∧
        ops.op8 D sem v () (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
        Tx1Reachability.afterPrepare (withConstants ops) D bytes proof k () none prepared scratch=ok (.Ok out) := by
  exact FirstComposition.first_current_prepared_new invalidAccountData (withConstants ops)
    D error bytes proof k out h

#print axioms constants_total
#print axioms zero_total
#print axioms source_ranges
#print axioms first_with_constants
end AspisR1CurrentCaller.ConcreteConstants
