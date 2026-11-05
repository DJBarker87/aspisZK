import NCX_Install
import NIS_EntryModel
set_option autoImplicit false
noncomputable section
namespace NIJ_EntryJoin
open Aeneas Aeneas.Std Result

theorem source (bytes : Slice U8) :
 NCX_Install.op34 bytes =
   (do let reply ← NIJ_EntryModel.body bytes
       ok (NCX_Install.mapReturn NCX_Carrier.entry reply)) := by
 unfold NCX_Install.op34
 rw [NIJ_EntryModel.source]

theorem cohort (base : AdapterRw.Ops) (bytes : Slice U8) :
 (NCX_Install.install base).op34 bytes =
   (do let reply ← NIJ_EntryModel.body bytes
       ok (NCX_Install.mapReturn NCX_Carrier.entry reply)) := source bytes

theorem digest_error_frame (base : AdapterRw.Ops) :
 (NCX_Install.install base).op43=base.op43 ∧
 (NCX_Install.install base).op44=base.op44 := ⟨rfl,rfl⟩

#print axioms source
#print axioms cohort
#print axioms digest_error_frame
end NIJ_EntryJoin
