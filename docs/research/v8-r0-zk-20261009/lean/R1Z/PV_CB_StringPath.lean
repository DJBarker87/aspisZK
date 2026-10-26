import R1Z.PV_CB_PathBorrow
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_StringPath
open Aeneas Aeneas.Std Result ProverRwFull
/-- UTF-8 bytes; no lossy decoding, path normalization, or allocation choice. -/
def bytes (s : String) : List U8 :=
  s.toByteArray.toList.map (fun b => { bv := b.toBitVec })
def borrow (s : String) : Result PDict_PathTypes.std.path.Path :=
  if h : (bytes s).length ≤ Usize.max then .ok ⟨⟨⟨⟨bytes s,h⟩⟩⟩⟩
  else .fail .panic
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CB_PathBorrow.native base)) :
    @ExternalFuns (PV_CB_PathBorrow.native base) :=
  letI : ExternalTypes := PV_CB_PathBorrow.native base
  {PV_CB_PathBorrow.selected base ops with op28 := borrow}
theorem op28_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CB_PathBorrow.native base)) (s : String) :
    (selected base ops).op28 s = borrow s := rfl
theorem op28_bytes (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CB_PathBorrow.native base)) (s : String)
    (h : (bytes s).length ≤ Usize.max) :
    (selected base ops).op28 s = .ok ⟨⟨⟨⟨bytes s,h⟩⟩⟩⟩ := by
  change borrow s = _
  simp only [borrow,dif_pos h]
#print axioms op28_installed
#print axioms op28_bytes
end R1Z.PV_CB_StringPath
