import NLU_Words
import NLU_Cell
set_option autoImplicit false
namespace AspisR1.NMO_TerminalWindows
open Aeneas Aeneas.Std AspisR1PublicPreparation
abbrev Claims := NLC_Finish.Claims
abbrev Alpha := NLC_Finish.Alpha
/-- Twelve native row/limb windows, with an arbitrary column in each.
These are exact argument-value clauses, not independent completed buffers. -/
def ClaimsWindow (actual expected : Claims) (row : Fin 3) (limb : Fin 4) : Prop :=
 ∀ column : Fin 29,
 NLU.word (NLU.cell (NLU.cell actual row.val row.isLt) column.val column.isLt) limb=
 NLU.word (NLU.cell (NLU.cell expected row.val row.isLt) column.val column.isLt) limb
theorem claims_complete (actual expected : Claims)
 (windows : ∀ row limb,ClaimsWindow actual expected row limb) : actual=expected := by
 apply NLU.cells_ext
 intro row hr
 apply NLU.cells_ext
 intro column hc
 apply NLU.word_ext
 intro limb
 exact windows ⟨row,hr⟩ limb ⟨column,hc⟩
def AlphaWindow (actual expected : Alpha) (limb : Fin 4) : Prop :=
 ∀ index : Fin 10,NLU.word (NLU.cell actual index.val index.isLt) limb=
 NLU.word (NLU.cell expected index.val index.isLt) limb
theorem alpha_complete (actual expected : Alpha)
 (windows : ∀ limb,AlphaWindow actual expected limb) : actual=expected := by
 apply NLU.cells_ext
 intro index hi
 apply NLU.word_ext
 intro limb
 exact windows limb ⟨index,hi⟩
#print axioms claims_complete
#print axioms alpha_complete
end AspisR1.NMO_TerminalWindows
