import NHU_MaskHelpers
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_Power
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

def chain (square : QM→Result QM) (multiply : QM→QM→Result QM) (value : QM) : Result QM := do
 let x2←square value
 let x4←square x2
 let x8←square x4
 let x16←square x8
 let x24←multiply x16 x8
 multiply x24 x2

/-- The retained emitted function, with six arithmetic packet boundaries.
The native cut is generated from the frozen body; no product is verified by
Kani. The complete canonical-domain law below discharges all six replies. -/
theorem source (value : QM) :
 AspisR1SelectedMaskProbe.state_only_hiding.mask_power_26 value=
 chain AspisR1SelectedMaskProbe.field.QM31.square
  AspisR1SelectedMaskProbe.field.QM31.mul value := rfl

/-- Canonicality of every intermediate follows from the closed child laws,
not a caller-selected successful chain. The inherited exact exponent theorem
is reused rather than reproved. -/
theorem result (value : QM) (canonical : Canonical value) :
 ∃ out,chain AspisR1SelectedMaskProbe.field.QM31.square
  AspisR1SelectedMaskProbe.field.QM31.mul value=ok out ∧
 Canonical out ∧ AspisR1.ExtractedMaskPower26.decode out=
  AspisR1.ExtractedMaskPower26.decode value^26 := by
 rw [←source]
 exact AspisR1.ExtractedMaskPower26.current_mask_power_26 value canonical

/-- Every product/square call in the native chronological log is on the
SAME canonical value returned by its predecessor packet. -/
theorem domains (value : QM) (canonical : Canonical value) :
 ∃ a b c d e f,
 AspisR1SelectedMaskProbe.field.QM31.square value=ok a ∧ Canonical a ∧
 AspisR1SelectedMaskProbe.field.QM31.square a=ok b ∧ Canonical b ∧
 AspisR1SelectedMaskProbe.field.QM31.square b=ok c ∧ Canonical c ∧
 AspisR1SelectedMaskProbe.field.QM31.square c=ok d ∧ Canonical d ∧
 AspisR1SelectedMaskProbe.field.QM31.mul d c=ok e ∧ Canonical e ∧
 AspisR1SelectedMaskProbe.field.QM31.mul e a=ok f ∧ Canonical f := by
 obtain ⟨a,ha,ca,_⟩:=AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact value canonical
 obtain ⟨b,hb,cb,_⟩:=AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact a ca
 obtain ⟨c,hc,cc,_⟩:=AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact b cb
 obtain ⟨d,hd,cd,_⟩:=AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact c cc
 obtain ⟨e,he,ce,_⟩:=AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact d c cd cc
 obtain ⟨f,hf,cf,_⟩:=AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact e a ce ca
 exact ⟨a,b,c,d,e,f,ha,ca,hb,cb,hc,cc,hd,cd,he,ce,hf,cf⟩

#print axioms domains
#print axioms source
#print axioms result
end AspisR1.NHU_Power
