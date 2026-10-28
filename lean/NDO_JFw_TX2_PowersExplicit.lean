import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_PowersExplicit
open Aeneas Aeneas.Std Result
abbrev E := FIo_Install.NE
abbrev decode := fun x : E => AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide x)
def entry (j : Fin 29) : E := FIo_Install.toE
  (JFr_TX2_Powers.value.val[j.val]'(by rw [JFr_TX2_Powers.value.property]; exact j.isLt))
def gamma : E := FIo_Install.toE JFo_Prepared.value.gamma

theorem meaning (j : Fin 29) : decode (entry j)=decode gamma^j.val := by
  have h := ((Classical.choose_spec JFo_Powers.source).2 j).2
  exact h

theorem identify (j : Fin 29) (x : E) (hx : FIo_WideValues.Canon x)
    (h : decode x=decode gamma^j.val) : entry j=x :=
  JFw_TX2_ValueUnique.native _ _ (JFr_TX2_Powers.canonical j) hx ((meaning j).trans h.symm)
#print axioms meaning
#print axioms identify
end AspisR1.JFw_TX2_PowersExplicit
end
