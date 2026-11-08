import NMX_R4_ProjectionRef
import NMX_R2_ArgsReify
set_option autoImplicit false
noncomputable section
namespace NMX_R4_ArgsPort
open Aeneas Aeneas.Std RSL

/-- Only the seven-account branch reifies a slice. Malformed lengths remain
source rejection arms, including lengths beyond every Rust representation. -/
theorem bounds (a : TX2_233.Args) (count : a.accounts.length = 7) :
 NMX_R2_ArgsReify.Bounds (NMX_R4_ProjectionRef.args a) := by
 constructor
 · change (a.accounts.map NMX_R4_AccountProjection.account).length ≤ Usize.max
   rw [List.length_map,count]
   scalar_tac
 · intro x member
   obtain ⟨original,_,same⟩ := List.mem_map.mp member
   subst x
   exact NMX_R4_AccountProjection.bounds original

#print axioms bounds
end NMX_R4_ArgsPort
end
