import NCX_Install
import NHY_RegistryModel
set_option autoImplicit false
noncomputable section
namespace NHY_RegistryJoin
open Aeneas Aeneas.Std Result

theorem source (bytes : Slice U8) :
 NCX_Install.op33 bytes =
   (do let reply ← NHY_RegistryModel.body bytes
       ok (NCX_Install.mapReturn NCX_Carrier.registry reply)) := by
 unfold NCX_Install.op33
 rw [NHY_RegistryModel.source]

theorem cohort (base : AdapterRw.Ops) (bytes : Slice U8) :
 (NCX_Install.install base).op33 bytes =
   (do let reply ← NHY_RegistryModel.body bytes
       ok (NCX_Install.mapReturn NCX_Carrier.registry reply)) := source bytes

theorem digest_error_frame (base : AdapterRw.Ops) :
 (NCX_Install.install base).op43=base.op43 ∧
 (NCX_Install.install base).op44=base.op44 := ⟨rfl,rfl⟩

#print axioms source
#print axioms cohort
#print axioms digest_error_frame
end NHY_RegistryJoin
