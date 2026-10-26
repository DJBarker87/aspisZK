import FIp_FinalSum
import FIp_PrefixFin
import FIp_PowersValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_FinalPolynomial
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open scoped BigOperators

theorem seven (parts k : Array NE 7#usize) (kappa out : NE)
    (hp : FIo_ArrayCanon.Holds parts) (hc : FIo_WideValues.Canon kappa)
    (powers : FIo_Native.weights.powers 7#usize kappa=ok k)
    (run : FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
      FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=
      ∑ j : Fin 7,decodeWide (wide kappa)^j.val*FIp_ArrayValue.value parts j.val := by
  have pk := FIp_PowersValue.powers 7#usize kappa k hc powers
  have sum := FIp_FinalSum.seven parts k hp pk.1 out run
  refine ⟨sum.1,?_⟩
  rw [sum.2,FIp_PrefixFin.sum_fin]
  apply Finset.sum_congr rfl
  intro j _
  rw [pk.2 j.val j.isLt]

#print axioms seven
end AspisR1.FIp_FinalPolynomial
end
