import NKB_CanonicalKBridge
set_option autoImplicit false
noncomputable section
namespace NKL_CanonicalKCarrier
open Aeneas Aeneas.Std Result AspisR1 NKB_CanonicalRange
open OraclePortCkptAbi4Decode CheckpointBytes3KDecode CheckpointBytes3ScalarShape
attribute [local instance] Classical.propDecidable

def toCaller (x : RawK) : K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def raw (b : Slice U8) (width : b.val.length=16) : RawK :=
 kWords (word b width 0) (word b width 1) (word b width 2) (word b width 3)

def selected (b : Slice U8) : Option K :=
 if width:b.val.length=16 then
  if Canonical (raw b width) then some (toCaller (raw b width)) else none
 else none

def mapResult {A B : Type} (f : A→B) : Result A→Result B
 | .ok x=>.ok (f x) | .fail e=>.fail e | .div=>.div

/-- Actual full decoder Result and payload transfer on every SAME16-byte call.
The off-domain extension is explicit; caller window lemmas establish width. -/
theorem decoder (b : Slice U8) (width : b.val.length=16) :
 mapResult (Option.map toCaller) (OraclePortCkptAbi2Extracted.decode_k_spec b)=ok (selected b) := by
 have h0 : OraclePortCkptAbi2Extracted.word_spec b 0#usize=ok (word b width 0) := by
  simpa [word] using CheckpointBytes3Word.word_total b 0#usize (by simp only [width];scalar_tac)
 have h1 : OraclePortCkptAbi2Extracted.word_spec b 4#usize=ok (word b width 1) := by
  simpa [word] using CheckpointBytes3Word.word_total b 4#usize (by simp only [width];scalar_tac)
 have h2 : OraclePortCkptAbi2Extracted.word_spec b 8#usize=ok (word b width 2) := by
  simpa [word] using CheckpointBytes3Word.word_total b 8#usize (by simp only [width];scalar_tac)
 have h3 : OraclePortCkptAbi2Extracted.word_spec b 12#usize=ok (word b width 3) := by
  simpa [word] using CheckpointBytes3Word.word_total b 12#usize (by simp only [width];scalar_tac)
 rw [CheckpointBytes3ScalarShape.k_shape b _ _ _ _ h0 h1 h2 h3]
 unfold selected raw
 simp only [dif_pos width]
 split <;> rfl

theorem selected_tag (b : Array U8 16#usize) :
 (selected b.to_slice).isSome=NKB_CanonicalKBridge.good b := by
 unfold selected
 simp only [dif_pos b.property]
 unfold raw NKB_CanonicalKBridge.good
 split <;> simp_all

set_option pp.proofs false
#print decoder
#print axioms decoder
#print axioms selected_tag
end NKL_CanonicalKCarrier
end
