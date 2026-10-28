import NCJ_FieldDomains
import NCJ_WordIdentity
set_option autoImplicit false
noncomputable section
namespace NCJ_FieldTotal
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def Canonical (part : Array U8 32#usize) : Prop :=
  ∀ i : Fin 8,(NBG_WideBytes.word part i.val).val<2147483647

def decode (part : Array U8 32#usize) : NE :=
  LPf_WideConstruction.value (NBG_WideBytes.word part 0) (NBG_WideBytes.word part 1)
    (NBG_WideBytes.word part 2) (NBG_WideBytes.word part 3)
    (NBG_WideBytes.word part 4) (NBG_WideBytes.word part 5)
    (NBG_WideBytes.word part 6) (NBG_WideBytes.word part 7)

theorem limbs (part : Array U8 32#usize) (canonical : Canonical part) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs (NBG_WideBytes.limbs part)=
      ok (some (decode part)) := by
  exact LPf_WideConstruction.source _ _ _ _ _ _ _ _
    (canonical 0) (canonical 1) (canonical 2) (canonical 3)
    (canonical 4) (canonical 5) (canonical 6) (canonical 7)

theorem canonical (part : Array U8 32#usize) (h : Canonical part) : canonE (decode part) :=
  ⟨⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩,⟨⟨h 4,h 5⟩,⟨h 6,h 7⟩⟩⟩

/-- No decoder success is assumed. Source-valid range and canonical bytes
construct the SAME field return, preserving exact selected surrounding bytes. -/
theorem source (bytes : Slice U8) (i : Usize)
    (bound : 32*(i.val+1)≤bytes.val.length)
    (valid : ∀ part : Array U8 32#usize,
      part.val=(bytes.val.drop (32*i.val)).take 32 → Canonical part) :
    ∃ part : Array U8 32#usize,
      part.val=(bytes.val.drop (32*i.val)).take 32 ∧
      FIo_Native.weights.field bytes i=ok (decode part) ∧ canonE (decode part) := by
  obtain ⟨part,selected,run⟩ := NBQ_FieldTotal.range bytes i bound
  have hc := valid part selected
  refine ⟨part,selected,?_,canonical part hc⟩
  rw [run,limbs part hc]
  rfl

#print axioms limbs
#print axioms canonical
#print axioms source
end NCJ_FieldTotal
