import NEG_RowIsolated.Funs
import Port26ROW_Row
set_option autoImplicit false
noncomputable section
namespace NEG_RowAssociation
open Aeneas Aeneas.Std Result
abbrev Power := NEG_RowIsolated.aspis_core.field.QM31

def toOld (p : Power) : Port23PUSH.field.QM31 :=
  ⟨⟨p.c0.a,p.c0.b⟩,⟨p.c1.a,p.c1.b⟩⟩

theorem emitted_to_owned (row : Array U64 4#usize) (p : Power)
    (basis : U32) (flush : Bool) :
    NEG_RowIsolated.update_residue_row row p basis flush =
      S7Kani2OwnedRow.residue_owned row (Port26ROW.toK (toOld p)) basis flush := by
  change Port23PUSH.verifier.update_residue_row Port25ARRAY.concrete row (toOld p) basis flush = _
  exact Port26ROW.row_complete row (toOld p) basis flush

#print axioms emitted_to_owned
end NEG_RowAssociation
end
