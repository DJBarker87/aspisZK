import NHT_COMBINED_IMPORT
import NHV_NEO_FixedWindow
import NEB_PureFrame

set_option autoImplicit false
namespace NEO_QuadraticTotal
open Aeneas Aeneas.Std Result

theorem result (bytes : Slice U8) (bound : 16≤bytes.val.length) :
 NEO_WindowV2.quadratic bytes=NEO_QuadraticCuts.cohort bytes := by
 have first := NEO_FixedWindow.range bytes 0#usize 8#usize 8#usize
  (by decide) (by change 8≤bytes.val.length; omega) (by decide)
 have second := NEO_FixedWindow.range bytes 8#usize 16#usize 8#usize
  (by decide) (by change 16≤bytes.val.length; exact bound) (by decide)
 exact NEO_QuadraticCuts.result bytes _ _ first second

theorem observe_injective (x y : AspisR1CandidateParser.field.QM31)
 (h : NEO_QuadraticCuts.observe x=NEO_QuadraticCuts.observe y) : x=y := by
 rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
 rcases y with ⟨⟨e,f⟩,⟨g,k⟩⟩
 simp [NEO_QuadraticCuts.observe,Array.make] at h
 rcases h with ⟨rfl,rfl,rfl,rfl⟩
 rfl

theorem complex_frame {S Event : Type} (state : S) (bytes : Slice U8)
 (bound : 8≤bytes.val.length) :
 NEB_PureFrame.run (Event:=Event) state (NEO_WindowV2.complex bytes)=
 NEB_PureFrame.run state (NEO_ComplexReference.cohort bytes) :=
 NEB_PureFrame.equality state _ _ (NEO_ComplexTotal.result bytes bound)

theorem quadratic_frame {S Event : Type} (state : S) (bytes : Slice U8)
 (bound : 16≤bytes.val.length) :
 NEB_PureFrame.run (Event:=Event) state (NEO_WindowV2.quadratic bytes)=
 NEB_PureFrame.run state (NEO_QuadraticCuts.cohort bytes) :=
 NEB_PureFrame.equality state _ _ (result bytes bound)

#print axioms result
#print axioms observe_injective
#print axioms complex_frame
#print axioms quadratic_frame
end NEO_QuadraticTotal
