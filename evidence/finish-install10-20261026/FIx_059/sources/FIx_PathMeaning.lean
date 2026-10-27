import FIx_PathLiteral
import FIx_PathModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PathMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIx_PathLiteral (Openings)

def coefficients (selector bit : K) (a a1 : Nat → K) : Fin (17#usize).val → K :=
  fun j=>if 9≤j.val then selector*bit*(a1 (8+(j.val-9))-a (1+(j.val-9)))
    else if 1≤j.val then selector*(1-bit)*(a1 (j.val-1)-a (1+(j.val-1)))
    else selector*(bit*(bit-1))

theorem value (selector : NQ) (o : Openings) (out : Array NQ 17#usize)
    (hs : Canon selector) (hz : canonical o.z) (hsucc : canonical o.succ_z)
    (success : pool_v1.pair_forest_semantic_terminal.path_lanes_literal selector o=ok out) :
    canonical out ∧ decoded out=coefficients (decode selector) (FIv_NativeArray.value o.z 0)
      (FIv_NativeArray.value o.z) (FIv_NativeArray.value o.succ_z) := by
  obtain ⟨bit,hbit,hb,hc,hv⟩ := FIx_PathLiteral.value selector o out hs hz hsucc success
  have bitValue : FIv_NativeArray.value o.z 0=decode bit := FIv_NativeArray.read o.z 0#usize bit hbit
  refine ⟨hc,?_⟩
  rw [hv,bitValue]
  funext j
  rw [FIx_PathModel.value selector bit o.z o.succ_z 8 0 _ j (by decide)]
  have hj : j.val<17 := j.isLt
  unfold coefficients FIx_PathModel.left FIx_PathModel.right
  by_cases h9 : 9≤j.val
  · rw [if_pos h9,if_pos (show 9+0≤j.val ∧ j.val<9+(0+8) by omega)]
  · rw [if_neg h9,if_neg (show ¬(9+0≤j.val ∧ j.val<9+(0+8)) by omega)]
    by_cases h1 : 1≤j.val
    · rw [if_pos h1,if_pos (show 1+0≤j.val ∧ j.val<1+(0+8) by omega)]
    · rw [if_neg h1,if_neg (show ¬(1+0≤j.val ∧ j.val<1+(0+8)) by omega)]
      have zero : j=(⟨0,by decide⟩ : Fin (17#usize).val) := Fin.ext (by omega)
      subst j
      unfold FIx_PathLiteral.initial
      rw [Function.update_self]
#print axioms value
end AspisR1.FIx_PathMeaning
end
