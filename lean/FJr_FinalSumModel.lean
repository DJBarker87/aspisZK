import FIp_FinalSum
import FIp_PowersValue
import FJr_FoldLinear
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_FinalSumModel
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open scoped BigOperators
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

theorem sumPrefix {N : Usize} (parts k : Array NE N) (n : Nat) :
    FIp_Prefix.sumPrefix parts k n=∑ j∈Finset.range n,FIp_ArrayValue.value k j*FIp_ArrayValue.value parts j := by
  induction n with
  | zero=>simp only [FIp_Prefix.zero,Finset.range_zero,Finset.sum_empty]
  | succ n ih=>rw [FIp_Prefix.succ,Finset.sum_range_succ,ih]

theorem value (parts k : Array NE 7#usize) (kappa out : NE)
    (cp : FIo_ArrayCanon.Holds parts) (ck : FIo_WideValues.Canon kappa)
    (pk : FIo_Native.weights.powers 7#usize kappa=ok k)
    (run : FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
      FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out)
    (rows : Fin 7 → Fin 1024 → FE) (f : Fin 64 → FE) (a0 a1 : FE)
    (values : ∀ j : Fin 7,FIp_ArrayValue.value parts j.val=RoundPairing.dot f
      (RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (rows j)))) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=RoundPairing.dot f
      (RoundPairing.dualFold a1 (RoundPairing.dualFold a0
        (fun i=>∑ j : Fin 7,decodeWide (wide kappa)^j.val*rows j i))) := by
  have powers := FIp_PowersValue.powers 7#usize kappa k ck pk
  have final := FIp_FinalSum.seven parts k cp powers.1 out run
  refine ⟨final.1,?_⟩
  rw [final.2,sumPrefix,←Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ j : Fin 7,decodeWide (wide kappa)^j.val*RoundPairing.dot f
        (RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (rows j))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [powers.2 j.val j.isLt,values j]
    _ = _ := FJr_FoldLinear.value a0 a1 (fun j : Fin 7=>decodeWide (wide kappa)^j.val) rows f

#print axioms sumPrefix
#print axioms value
end AspisR1.FJr_FinalSumModel
end
