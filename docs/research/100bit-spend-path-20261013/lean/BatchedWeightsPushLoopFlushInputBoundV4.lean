import BatchedWeightsPushLoopAllPrefixV11
import AspisR1BatchedFoldSourceStep
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace BatchedWeightsPushLoopFlushInputBoundV4
open AspisR1BatchedWeightsPushLoopAllPrefixV11
abbrev BW := AspisR1BatchedWeightsPushLoopAllPrefixV11.BW
abbrev Usize := UScalar UScalarTy.Usize
abbrev M := AspisR1BatchedWeightsPushLoopAllPrefixV11.M
abbrev Q := AspisR1BatchedWeightsPushLoopAllPrefixV11.Q
abbrev Range := core.ops.range.Range Usize

def limbsOf (power : Q) : Array Std.U32 4#usize :=
  Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]

private theorem limbsOf_lt (power : Q)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P) :
    ∀ k : Usize, ∀ hk : k.val < 4,
      limbAt (limbsOf power) k hk < AspisR1BatchedFoldSourceStep.modulus := by
  have hP : AspisV8R17.RawReducer.P = AspisR1BatchedFoldSourceStep.modulus := by
    norm_num [AspisV8R17.RawReducer.P, AspisR1BatchedFoldSourceStep.modulus]
  rw [hP] at ha hb hc hd
  intro k hk
  have hcases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by omega
  rcases hcases with h | h | h | h
  · have hkeq : k = 0#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [limbsOf, limbAt, Array.make] using ha
  · have hkeq : k = 1#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [limbsOf, limbAt, Array.make] using hb
  · have hkeq : k = 2#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [limbsOf, limbAt, Array.make] using hc
  · have hkeq : k = 3#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [limbsOf, limbAt, Array.make] using hd

theorem push_loop_flush_input_lt_u64
    (index : Usize) (initial : BW) (power : Q) (basis : M)
    (hindex : index.val < initial.raw.length)
    (hraw : ∀ k : Usize, ∀ hk : k.val < 4,
      cellAt initial index hindex k hk <
        2^34 + (initial.terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hflush : initial.terms.val % 4 = 3) :
    ∃ mid : BW, ∃ hm : index.val < mid.raw.length,
      AspisR1BatchedWeightsExtraction.batched_weights.BatchedWeights.push_loop
        ({ start := 0#usize, «end» := 4#usize } : Range)
        initial index basis (limbsOf power) = .ok mid ∧
      LoopPost index initial hindex (limbsOf power) basis mid ∧
      ∀ k : Usize, ∀ hk : k.val < 4,
        cellAt mid index hm k hk < 2^64 := by
  obtain ⟨mid,hloop,hpost⟩ := push_loop_all_prefix index initial power basis
    hindex hraw ha hb hc hd hbasis
  have hP : AspisV8R17.RawReducer.P = AspisR1BatchedFoldSourceStep.modulus := by
    norm_num [AspisV8R17.RawReducer.P, AspisR1BatchedFoldSourceStep.modulus]
  have hlimbs := limbsOf_lt power ha hb hc hd
  have hbasis' : basis.val < AspisR1BatchedFoldSourceStep.modulus := by
    rw [← hP]; exact hbasis
  have hcap : AspisR1BatchedAllPrefix.cap = AspisR1BatchedFoldSourceStep.productCap := rfl
  have hsafe : 2^34 + 4 * AspisR1BatchedFoldSourceStep.productCap < 2^64 := by
    norm_num [AspisR1BatchedFoldSourceStep.productCap]
  let hm : index.val < mid.raw.length := hpost.2.1
  have hcells := hpost.2.2
  refine ⟨mid,hm,hloop,hpost,?_⟩
  intro k hk
  have hbase : cellAt initial index hindex k hk < 2^34 + 3 * AspisR1BatchedFoldSourceStep.productCap := by
    have := hraw k hk
    rw [hflush, hcap] at this
    exact this
  have hprod : limbAt (limbsOf power) k hk * basis.val ≤
      AspisR1BatchedFoldSourceStep.productCap := by
    exact AspisR1BatchedFoldSourceStep.product_bound (hlimbs k hk) hbasis'
  have hcell : cellAt mid index hm k hk =
      expectedCell initial index hindex (limbsOf power) basis k hk := hcells k hk
  rw [hcell, expectedCell]
  omega

#print axioms limbsOf_lt
#print axioms push_loop_flush_input_lt_u64
end BatchedWeightsPushLoopFlushInputBoundV4
