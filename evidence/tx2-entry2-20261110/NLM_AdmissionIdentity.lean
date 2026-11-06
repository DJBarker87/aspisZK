import NLM_CellIdentity
import NLF_SevenAccounts
set_option autoImplicit false
noncomputable section
namespace NLM_AdmissionIdentity
open AspisR1 AspisR1.S2W_D189Entry NLM_Snapshot
/-- Exactly the accepted seven-field admission item. Equal keys and equal
SDK data-cell identities are equivalent, not independently selected maps. -/
theorem cells (e : Entry)
 (runtime : AdapterRw.RuntimeEntrypointAdmission e.heap (fun a=>(NLM_RuntimeInput.records e a).key) 7)
 (a b t : Nat) (owned : List NLM_Snapshot.Owned) (ha : a<7) (hb : b<7) :
 (guard (ready e t owned) a).cell=(guard (ready e t owned) b).cell ↔
 (NLM_RuntimeInput.records e a).key=(NLM_RuntimeInput.records e b).key :=
 NLF_SevenAccounts.tx2_cell_identity e.heap (NLM_RuntimeInput.records e)
  (NLM_RuntimeInput.money e) runtime a b ha hb
#print cells
#print axioms cells
end NLM_AdmissionIdentity
