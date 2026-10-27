import RPu_FJf_DotPushValue
import RPu_JFv_TX2_DotFinishMeaning
set_option autoImplicit false
namespace AspisR1.FJf_DotFinishValue
open Aeneas Aeneas.Std Result
open FJf_DotLane (Dot)

theorem at_fin (a : Array U64 4#usize) (j : Fin 4) :
    FJf_U64Array.cell a j.val=JFv_TX2_DotFinishMeaning.cell a j := by
  unfold FJf_U64Array.cell JFv_TX2_DotFinishMeaning.cell
  rw [List.getElem?_eq_getElem (by rw [a.property];exact j.isLt)]
  rfl

theorem value (dot : Dot) (out : FIo_Native.fast_pairing.canonical.Q)
    (run : FIo_Native.fast_pairing.canonical.Dot.finish dot=ok out) :
    JFs_TX2_DotFinish.Canon out ∧ ∀ j : Fin 4,
      (JFv_TX2_DotFinishMeaning.cell out j).val=
        (FJf_U64Array.cell dot.sums j.val).val%2147483647 := by
  obtain ⟨out',hr,hc,hv⟩ := JFv_TX2_DotFinishMeaning.source dot
  have same := Result.ok.inj (hr.symm.trans run)
  subst out
  exact ⟨hc,fun j => by rw [at_fin];exact hv j⟩
#print axioms at_fin
#print axioms value
end AspisR1.FJf_DotFinishValue
