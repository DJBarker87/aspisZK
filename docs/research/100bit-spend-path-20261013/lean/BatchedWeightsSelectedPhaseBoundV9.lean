import BatchedWeightsPushOuterNoFlushV3
import BatchedWeightsPushOuterFlushV15
import BatchedWeightsPushLoopFlushInputBoundV4
import AspisR1BatchedFoldSourceStep
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsSelectedPhaseBoundV1
open AspisR1BatchedWeightsExtraction
open AspisR1BatchedWeightsPushLoopAllPrefixV11
abbrev BW := batched_weights.BatchedWeights
abbrev Usize := UScalar UScalarTy.Usize
abbrev M := aspis_core.field.M31
abbrev Q := aspis_core.field.QM31

private theorem limbs_lt (power : Q)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P) :
    ∀ k : Usize, ∀ hk : k.val < 4,
      limbAt (BatchedWeightsPushLoopFlushInputBoundV4.limbsOf power) k hk <
        AspisR1BatchedFoldSourceStep.modulus := by
  have hP : AspisV8R17.RawReducer.P = AspisR1BatchedFoldSourceStep.modulus := by
    norm_num [AspisV8R17.RawReducer.P, AspisR1BatchedFoldSourceStep.modulus]
  rw [hP] at ha hb hc hd
  intro k hk
  have hcases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by omega
  rcases hcases with h | h | h | h
  · have hkeq : k = 0#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [BatchedWeightsPushLoopFlushInputBoundV4.limbsOf, limbAt, Array.make] using ha
  · have hkeq : k = 1#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [BatchedWeightsPushLoopFlushInputBoundV4.limbsOf, limbAt, Array.make] using hb
  · have hkeq : k = 2#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [BatchedWeightsPushLoopFlushInputBoundV4.limbsOf, limbAt, Array.make] using hc
  · have hkeq : k = 3#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [BatchedWeightsPushLoopFlushInputBoundV4.limbsOf, limbAt, Array.make] using hd

/-- A selected generated push in phases zero through two advances that cell
from the old global envelope to the next phase envelope.  This is the actual
outer push result, not just the inner loop's arithmetic state. -/
theorem selected_nonflush_cell_next_bound
    (index : Usize) (initial out : BW) (power : Q) (basis : M)
    (hindex : index.val < initial.raw.length)
    (hraw : ∀ k : Usize, ∀ hk : k.val < 4,
      cellAt initial index hindex k hk <
        2^34 + (initial.terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hphase : initial.terms.val % 4 < 3)
    (hpush : batched_weights.BatchedWeights.push initial index power basis = .ok out) :
    ∃ hout : index.val < out.raw.length,
      ∀ k : Usize, ∀ hk : k.val < 4,
        cellAt out index hout k hk <
          2^34 + ((initial.terms.val + 1) % 4) * AspisR1BatchedAllPrefix.cap := by
  have hphase3 : initial.terms.val % 4 ≠ 3 := by omega
  obtain ⟨mid,hloop,houter,hterms⟩ :=
    BatchedWeightsPushOuterNoFlushV3.push_nonflush_success index initial power basis
      hindex hraw ha hb hc hd hbasis hphase3
  have heq : out = mid := Result.ok.inj (hpush.symm.trans houter)
  subst out
  obtain ⟨mid',hloop',hpostLoop⟩ :=
    AspisR1BatchedWeightsPushLoopAllPrefixV11.push_loop_all_prefix index initial power basis
      hindex hraw ha hb hc hd hbasis
  have hmEq : mid = mid' := Result.ok.inj (hloop.symm.trans (by
      simpa [BatchedWeightsPushLoopFlushInputBoundV4.limbsOf] using hloop'))
  subst mid
  have hP : AspisV8R17.RawReducer.P = AspisR1BatchedFoldSourceStep.modulus := by
    norm_num [AspisV8R17.RawReducer.P, AspisR1BatchedFoldSourceStep.modulus]
  have hcap : AspisR1BatchedAllPrefix.cap = AspisR1BatchedFoldSourceStep.productCap := rfl
  have hlimbs := limbs_lt power ha hb hc hd
  have hbasis' : basis.val < AspisR1BatchedFoldSourceStep.modulus := by
    rw [← hP]; exact hbasis
  refine ⟨hpostLoop.2.1, ?_⟩
  intro k hk
  have hprod : limbAt (BatchedWeightsPushLoopFlushInputBoundV4.limbsOf power) k hk * basis.val ≤
      AspisR1BatchedFoldSourceStep.productCap :=
    AspisR1BatchedFoldSourceStep.product_bound (hlimbs k hk) hbasis'
  have hlimbEq : limbAt (BatchedWeightsPushLoopFlushInputBoundV4.limbsOf power) k hk =
      limbAt (Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]) k hk := rfl
  have hprod' : limbAt (Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]) k hk * basis.val ≤
      AspisR1BatchedFoldSourceStep.productCap := by rw [← hlimbEq]; exact hprod
  have hvalue := hpostLoop.2.2 k hk
  rw [expectedCell] at hvalue
  rw [← hlimbEq] at hvalue
  have hbase := hraw k hk
  rw [hcap] at hbase
  have hphaseCases : initial.terms.val % 4 = 0 ∨
      initial.terms.val % 4 = 1 ∨ initial.terms.val % 4 = 2 := by omega
  have hnext : (initial.terms.val + 1) % 4 = initial.terms.val % 4 + 1 := by
    rcases hphaseCases with h0 | h1 | h2 <;> omega
  rw [hvalue, hnext, hcap]
  have hbase' : cellAt initial index hindex k hk <
      2^34 + (initial.terms.val % 4) * AspisR1BatchedFoldSourceStep.productCap := by
    exact hbase
  have hsum : cellAt initial index hindex k hk +
      limbAt (BatchedWeightsPushLoopFlushInputBoundV4.limbsOf power) k hk * basis.val <
      2^34 + (initial.terms.val % 4) * AspisR1BatchedFoldSourceStep.productCap +
        AspisR1BatchedFoldSourceStep.productCap := by omega
  calc
    _ < 2^34 + (initial.terms.val % 4) * AspisR1BatchedFoldSourceStep.productCap +
        AspisR1BatchedFoldSourceStep.productCap := hsum
    _ = 2^34 + (initial.terms.val % 4 + 1) * AspisR1BatchedFoldSourceStep.productCap := by
      rw [Nat.add_mul, one_mul]
      omega

#print axioms selected_nonflush_cell_next_bound
end BatchedWeightsSelectedPhaseBoundV1
