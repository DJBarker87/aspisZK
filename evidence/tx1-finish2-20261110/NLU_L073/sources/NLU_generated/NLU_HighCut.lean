import NLU_Words
import NLU_Cell
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_High
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NLU (Q word)
abbrev Claims := NLC_Finish.Claims
def high (claims : Claims) (i : Fin 10) : Q :=
 NLU.cell (NLU.cell claims 0 (by decide)) (16+i.val) (by have h:=i.isLt;change 16+i.val<29;omega)
structure Observation where
 value : Q
 claims : Claims
abbrev Native := Claims → Fin 10 → Observation
/-- Reviewed transcription of programs/r1-cost-probe/src/NLU_program.rs,
SHA256 b4bfd86dfa299c552474319448c674742024ac9fb5b2a36df66f6081d11a9125,
NLU_K001/2 and NLU_K003/4. Source helper NLI_rounds.rs is pinned in
NLU_SOURCE_PINS.json. Literal selected assertion: "if frame {
word(claims[row][col],j)==before } else { word(actual,j)==expected }".
The pairs are native support; physical parent integration still needs review.
Reviewed transcription of NLU_K001/2 and NLU_K003/4, pending pair
validation and ledger review. Literal native assertions:
value word(actual,j)==word(claims[0][16+i],j), or frame
word(claims[row][col],j)==before, with i<10,j<4,row<3,col<29.
No initialization/canonicality/success or destination-tail fact is added.
Harness sha256 is pinned by each receipt's setup/source snapshot. -/
def Cut (native : Native) : Prop := ∀ claims i,
 (∀ j,word (native claims i).value j=word (high claims i) j) ∧
 (∀ row (hr : row<3) col (hc : col<29) j,
  word (NLU.cell (NLU.cell (native claims i).claims row hr) col hc) j=
  word (NLU.cell (NLU.cell claims row hr) col hc) j)
theorem value (native : Native) (cut : Cut native) (claims : Claims) (i : Fin 10) :
 (native claims i).value=high claims i :=
 NLU.word_ext _ _ (cut claims i).1
theorem frame (native : Native) (cut : Cut native) (claims : Claims) (i : Fin 10) :
 (native claims i).claims=claims := by
 apply NLU.cells_ext
 intro row hr
 apply NLU.cells_ext
 intro col hc
 apply NLU.word_ext
 intro j
 exact (cut claims i).2 row hr col hc j
/-- Scalar native windows compose to one returned field and the SAME whole
Claims source frame. This remains conditional support, never a136 root. -/
theorem complete (native : Native) (cut : Cut native) (claims : Claims) (i : Fin 10) :
 native claims i=⟨high claims i,claims⟩ := by
 have hv:=value native cut claims i
 have hf:=frame native cut claims i
 cases h : native claims i with
 | mk v c => simp only [h] at hv hf;cases hv;cases hf;rfl
#print axioms value
#print axioms frame
#print axioms complete
end AspisR1.NLU_High
end
