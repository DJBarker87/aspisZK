import RPu_FJl_ScalarValues
import RPu_FJi_BaseDot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_BaseLiteral
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical
open scoped BigOperators
abbrev E := AspisWideTower.WideExact
def scalar (c : MixedLeafEncoding.C1) (s : Fin 4) (n : Nat) : E :=
  ExactBaseProjection.embed ((c s).1 ⟨n%26,Nat.mod_lt _ (by decide)⟩)
/-- Symbolic source prefix sum, in the literal C1 coordinates and SAME gamma. -/
theorem value (q : Array U8 608#usize) (g : Array FIo_FieldBridge.NE 29#usize)
    (gamma : E) (powers : ∀ l : Fin 29,FIp_ArrayValue.value g l.val=gamma^l.val)
    (c : MixedLeafEncoding.C1) (decoded : MixedLeafDecoder.decodeC1 ((bytesOf q.val).take 480)=some c)
    (s : Fin 4) (slot : Usize) (hs : slot.val=s.val)
    (reads : ∀ n,n<26 → FJl_InnerReads.Read q slot n) (n : Nat) (bound : n≤26) :
    FJi_BaseDot.sumTo q g slot n=∑ l ∈ Finset.range n,gamma^l*scalar c s l := by
  induction n with
  | zero => simp only [FJi_BaseDot.sumTo,Finset.range_zero,Finset.sum_empty]
  | succ n ih =>
    rw [FJi_BaseDot.sumTo,ih (by omega),Finset.sum_range_succ]
    have hn : n<26 := by omega
    have hn29 : n<29 := by omega
    rw [powers ⟨n,hn29⟩,FJl_ScalarValues.value q c decoded s slot hs reads ⟨n,hn⟩]
    have idx : (⟨n%26,Nat.mod_lt n (by decide)⟩ : Fin 26)=⟨n,hn⟩ := Fin.ext (Nat.mod_eq_of_lt hn)
    simp only [scalar,idx,Fin.val_mk]
#print axioms value
end AspisR1.FJl_BaseLiteral
end
