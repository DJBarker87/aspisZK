import CurrentClaimScalarReads
import ClaimDotConcreteAdapterV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimScalar
open Concrete AspisR1S5ClaimDotConcreteAdapter

def SelectedSource {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (point l : Usize) (scalar : aspis_core.field.QM31) : Prop :=
  (point ≤ 2#usize → ∃ row, Array.index_usize sem.claims point=Result.ok row ∧
    Array.index_usize row l=Result.ok scalar) ∧
  (point=3#usize → Array.index_usize sem.extra l=Result.ok scalar) ∧
  (point=4#usize → Array.index_usize sem.before_z1 l=Result.ok scalar) ∧
  (point=5#usize → ∃ parsed, ClaimParser.field y1 l=Result.ok parsed ∧
    Canonical parsed ∧ scalar=parsed.c0)

theorem successful_concrete_read_selected_source {H : Type}
    (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (point l : Usize)
    (scalar : aspis_core.field.QM31)
    (h : read (concreteOps rawFn) sem y1 point l=Result.ok scalar) :
    SelectedSource sem y1 point l scalar := by
  refine ⟨?_,?_,?_,?_⟩
  · intro hp
    exact read_claims_success (concreteOps rawFn) sem y1 point l scalar hp h
  · intro hp; subst point
    exact read_extra_success (concreteOps rawFn) sem y1 l scalar h
  · intro hp; subst point
    exact read_before_z1_success (concreteOps rawFn) sem y1 l scalar h
  · intro hp; subst point
    simp only [read,show ¬(5#usize ≤ 2#usize) from by decide,if_false,
      show (5#usize).val=5 from rfl] at h
    change (do let parsed ← ClaimParser.field y1 l; Result.ok parsed.c0)=Result.ok scalar at h
    cases hr : ClaimParser.field y1 l with
    | fail e => simp only [hr,bind_tc_fail] at h; cases h
    | div => simp only [hr,bind_tc_div] at h; cases h
    | ok parsed =>
      simp only [hr,bind_tc_ok] at h
      exact ⟨parsed,rfl,(ClaimParser.field_success y1 l parsed hr).1,(Result.ok.inj h).symm⟩

#print axioms successful_concrete_read_selected_source
end AspisR1CurrentPreparedClaim.ClaimScalar
