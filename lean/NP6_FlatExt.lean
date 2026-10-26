import NP6_ClaimsExt
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_FlatExt
open Aeneas Aeneas.Std AspisR1ClaimsUnrolledParent

def fields (out : Claims) (k : Fin 87) (l : Fin 4) : Nat :=
  NP6_ClaimsExt.limb
    (NP6_ClaimsExt.cell out ⟨k.val/29,by omega⟩ ⟨k.val%29,Nat.mod_lt _ (by decide)⟩) l

theorem injective (a b : Claims) (same : fields a = fields b) : a = b := by
  apply NP6_ClaimsExt.claims_ext
  intro p j l
  have bound : 29*p.val+j.val<87 := by omega
  have quotient : (29*p.val+j.val)/29=p.val := by omega
  have remainder : (29*p.val+j.val)%29=j.val := by omega
  have point := congrFun (congrFun same ⟨29*p.val+j.val,bound⟩) l
  simpa only [fields,quotient,remainder] using point

#print axioms injective
end AspisR1.NP6_FlatExt
end
