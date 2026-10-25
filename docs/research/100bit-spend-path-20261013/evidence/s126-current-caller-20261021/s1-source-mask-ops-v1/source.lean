import S1FinishMaskSourceV1
import S1FinishSelectorsV1
import S1SemanticRootCopyV1
set_option autoImplicit false
namespace AspisS1SourceMaskOps
open Aeneas Aeneas.Std Result
open AspisS1ExtractedRoundChildren (MainQM)
abbrev ProbeQM := AspisR1SelectedMaskProbe.field.QM31

def toProbe (q : MainQM) : ProbeQM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromProbe (q : ProbeQM) : MainQM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def probeArray {n : Usize} (a : Array MainQM n) : Array ProbeQM n :=
  ⟨a.val.map toProbe, by simpa using a.property⟩
def resultFromProbe : Result ProbeQM → Result MainQM
  | .ok q => .ok (fromProbe q)
  | .fail e => .fail e
  | .div => .div
def mask (c1 : Array MainQM 16#usize) (other : Array MainQM 10#usize)
    (g : MainQM) (alpha : Array MainQM 10#usize) : Result MainQM :=
  resultFromProbe (AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value
    (probeArray c1) (probeArray other) (toProbe g) (probeArray alpha))

/-- Only the two actual selector/mask operations are installed here. Every
other full finish operation retains the supplied dictionary's semantics. -/
def install (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    AspisR1PublicPreparation.FinishModel.Boundaries :=
  {B with fromFn := fun {T F} n callback state =>
    AspisR1SelectedMaskProbe.core.array.from_fn n callback state
    mask := mask}

theorem root_copy_commutes (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    AspisR1PublicPreparation.S1SemanticRootCopy.install (install B) =
      install (AspisR1PublicPreparation.S1SemanticRootCopy.install B) := rfl

#print axioms mask
#print axioms root_copy_commutes
end AspisS1SourceMaskOps
