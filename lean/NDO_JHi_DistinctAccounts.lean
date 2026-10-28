import NDO_JHg_World
import JHd_KeyStd
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_DistinctAccounts
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers JHg_World
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.publicInput JFx_NativeBytes.checkpoint JHb_Header.account
/-- The exact seven snapshots constructed in authenticate_asq8_accounts. -/
def value : Array AdapterRw.Cuts.Account 7#usize :=
  Array.make 7#usize [e2.snapshot 0 58295 58295,e2.snapshot 1 384 384,
    e2.snapshot 2 192 192,e2.snapshot 3 768 768,e2.snapshot 4 128 256,
    e2.snapshot 5 192 320,e2.snapshot 6 1768 1768]

theorem count : value.val.length=7 := value.property
#print axioms count
end AspisR1.JHi_DistinctAccounts
end
