import R1Z.ProverCommitNativeSquare49
/-! Canonical source negation and raw zero predicates. -/
set_option autoImplicit false
namespace R1Z.ProverCommitNativeNeg49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitNativeC49
open AspisV8R15.ExactTowerBase
abbrev P : Nat := AspisCircleGroupOrder.P

theorem neg_word (x : U32) (hx : x.val<P) :
    ∃ z : U32, field.M31.neg x=ok z ∧ z.val<P ∧
      (z.val : M31Exact)=-(x.val : M31Exact) := by
  by_cases hz : x=0#u32
  · refine ⟨0#u32,?_,by decide,?_⟩
    · simp only [field.M31.neg,hz,if_true]
    · rw [hz];change (0 : M31Exact)=-0;exact neg_zero.symm
  · let z := U32.wrapping_sub field.P x
    have hv : z.val=P-x.val := by
      have hp : field.P.val=P := by rw [field.P];rfl
      dsimp only [z]
      rw [U32.wrapping_sub_val_eq,hp,UScalar.size_def]
      change (P+(2^32-x.val))%2^32=P-x.val
      rw [show P+(2^32-x.val)=(P-x.val)+2^32 by have hh : P=2147483647 := rfl;omega,Nat.add_mod]
      simp only [Nat.mod_self,Nat.add_zero,Nat.mod_mod]
      apply Nat.mod_eq_of_lt
      change P-x.val<2^32
      have hh : P=2147483647 := rfl
      omega
    have hpos : 0<x.val := by
      have hn : x.val≠0 := by intro he;apply hz;exact UScalar.eq_of_val_eq he
      omega
    refine ⟨z,?_,by rw [hv];omega,?_⟩
    · simp only [field.M31.neg,hz,if_false,lift,bind_tc_ok];rfl
    · rw [hv,Nat.cast_sub (Nat.le_of_lt hx)]
      rw [show (P : M31Exact)=0 from ZMod.natCast_self P,zero_sub]

theorem neg (x : Old.C) (hx : Canonical x) :
    ∃ z : Old.C, field.CM31.neg (source x)=ok (source z) ∧
      Canonical z ∧ value z= -value x := by
  obtain ⟨a,ha,hca,hva⟩ := neg_word x.a hx.1
  obtain ⟨b,hb,hcb,hvb⟩ := neg_word x.b hx.2
  refine ⟨⟨a,b⟩,?_,⟨hca,hcb⟩,?_⟩
  · simp only [field.CM31.neg,source,ProverCommitRelease47.convC,fromC,ha,hb,bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · exact hva
    · exact hvb

theorem zero_c (x : Old.C) :
    field.CM31.is_zero (source x)=ok (decide (x.a=0#u32 ∧ x.b=0#u32)) := by
  by_cases ha : x.a=0#u32 <;> by_cases hb : x.b=0#u32 <;>
    simp [field.CM31.is_zero,field.M31.is_zero,source,ProverCommitRelease47.convC,fromC,ha,hb]

#print axioms neg_word
#print axioms neg
#print axioms zero_c
end R1Z.ProverCommitNativeNeg49
