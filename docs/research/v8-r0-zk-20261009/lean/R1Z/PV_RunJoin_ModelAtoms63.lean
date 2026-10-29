import R1Z.PV_RunJoin_ActualPoint59
import R1Z.PV_RunJoin_LinkR24Discharged54
/-! MODEL only: small explicit carriers for the simultaneous witness search.
These atoms alone do not establish Produced or the nine links. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ModelAtoms63
open Aeneas Aeneas.Std
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitWideOps48
open ProverCommitValueRange47 (embed)
open AspisR1.ExtractedCurrentQM31Exact (decode)
def zero : Old.Q := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def one : Old.Q := ⟨⟨1#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
theorem zero_canonical : Canonical zero := by decide
theorem one_canonical : Canonical one := by decide
theorem zero_decode : decode zero=0 := rfl
theorem one_decode : decode one=1 := rfl
def challenges : R0Z.HonestView.Challenges Exact where
  sem := fun _ => 0
  circle := fun _ => ⟨(1,0),by simp⟩
  opening := fun _ => 0
  queries := {0}
def data : PV_RunJoin_OpeningImages54.Data where
  c := fun _ _ => zero
  p := fun _ => zero
  x0 := one
  y0 := zero
  x1 := one
  y1 := zero
  g := (zero,zero)
  k := (zero,zero)
  a := (zero,zero)
  b := (zero,zero)
  ch := challenges

theorem coefficients : PV_RunJoin_OpeningImages54.Coefficients data := by
  intro _ _ _ _
  exact zero_canonical

theorem sample : PV_RunJoin_OpeningImages54.Sample data := by
  constructor
  · intro _ _; exact zero_canonical
  · exact one_canonical
  · exact zero_canonical
  · exact one_canonical
  · exact zero_canonical
  · exact ⟨zero_canonical,zero_canonical⟩
  · exact ⟨zero_canonical,zero_canonical⟩
  · exact ⟨zero_canonical,zero_canonical⟩
  · exact ⟨zero_canonical,zero_canonical⟩
  · funext i
    change embed (decode zero)=0
    rw [zero_decode]; exact map_zero _
  · change embed (decode one)=1
    rw [one_decode]; exact map_one _
  · change embed (decode zero)=0
    rw [zero_decode]; exact map_zero _
  · change embed (decode one)=1
    rw [one_decode]; exact map_one _
  · change embed (decode zero)=0
    rw [zero_decode]; exact map_zero _
  · rfl
  · rfl
  · rfl
  · rfl

#print axioms zero
#print axioms one
#print axioms zero_canonical
#print axioms one_canonical
#print axioms zero_decode
#print axioms one_decode
#print axioms challenges
#print axioms data
#print axioms coefficients
#print axioms sample
end R1Z.PV_RunJoin_ModelAtoms63
