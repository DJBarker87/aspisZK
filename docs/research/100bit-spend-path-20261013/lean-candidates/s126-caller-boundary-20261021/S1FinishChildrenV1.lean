import S1FinishMaskSourceV1
import S1ExtractedRoundChildrenV1
import S1SemanticCircleV1
import S1SemanticRootCopyV1
import TerminalArrayFromFnModelV4Clean
set_option autoImplicit false
namespace AspisS1FinishChildren
open Aeneas Aeneas.Std Result
open AspisS1ExtractedRoundChildren

abbrev MainClaims := Array (Array MainQM 29#usize) 3#usize
abbrev Claims := AspisR1PublicPreparation.r1_wire.Prefix →
  Result (core.result.Result MainClaims AspisR1PublicPreparation.r1_wire.Error)
abbrev Terminal := AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public →
  MainClaims → Array MainQM 10#usize → AspisR1PublicPreparation.r1_wire.Challenges →
  Result (core.result.Result MainQM AspisR1PublicPreparation.aspis_core.state_only_prefix.r0.Error)
abbrev ProbeQM := AspisR1SelectedMaskProbe.field.QM31

def toProbe (q : MainQM) : ProbeQM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromProbe (q : ProbeQM) : MainQM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def probeArray {n : Usize} (a : Array MainQM n) : Array ProbeQM n :=
  ⟨a.val.map toProbe, by simpa using a.property⟩
def resultFromProbe : Result ProbeQM → Result MainQM
  | .ok q => .ok (fromProbe q)
  | .fail e => .fail e
  | .div => .div

def add (x y : MainQM) : Result MainQM :=
  genResultToMain (AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (mainToGen x) (mainToGen y))
def mul (x y : MainQM) : Result MainQM :=
  genResultToMain (AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (mainToGen x) (mainToGen y))
def mask (c1 : Array MainQM 16#usize) (other : Array MainQM 10#usize)
    (g : MainQM) (alpha : Array MainQM 10#usize) : Result MainQM :=
  resultFromProbe (AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value
    (probeArray c1) (probeArray other) (toProbe g) (probeArray alpha))

/-- Six concrete finish operations. The two remaining source interfaces are
the complete claims producer and terminal evaluator, with all Rust/ambient
errors retained. This is an extracted-source installation, not a claim that
native SDK/Std/abort transport has already been proved. -/
def install (claims : Claims) (terminal : Terminal) :
    AspisR1PublicPreparation.FinishModel.Boundaries := {
  fromFn := fun {T F} n callback state => AspisR1SelectedMaskProbe.core.array.from_fn n callback state
  mask := mask
  add := add
  mul := mul
  terminal := terminal
  circle := AspisR1PublicPreparation.S1CircleCarrier.circle
  unwrapRoot := AspisR1PublicPreparation.S1SemanticRootCopy.unwrapRoot
  claims := claims
}

theorem coordinates_roundtrip (q : MainQM) : fromProbe (toProbe q) = q := by
  cases q with
  | mk c0 c1 => cases c0; cases c1; rfl

theorem mask_exact (claims : Claims) (terminal : Terminal)
    (c1 : Array MainQM 16#usize) (other : Array MainQM 10#usize)
    (g : MainQM) (alpha : Array MainQM 10#usize) :
    (install claims terminal).mask c1 other g alpha =
      resultFromProbe (AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value
        (probeArray c1) (probeArray other) (toProbe g) (probeArray alpha)) := rfl

theorem root_copy_idempotent (claims : Claims) (terminal : Terminal) :
    AspisR1PublicPreparation.S1SemanticRootCopy.install (install claims terminal) =
      install claims terminal := rfl

theorem circle_installed (claims : Claims) (terminal : Terminal) :
    AspisR1PublicPreparation.S1SemanticCircle.install (install claims terminal) =
      install claims terminal := rfl

theorem from_fn_exact (claims : Claims) (terminal : Terminal) {T F : Type}
    (n : Usize) (callback : core.ops.function.FnMut F Usize T) (state : F) :
    (install claims terminal).fromFn n callback state =
      AspisR1SelectedMaskProbe.core.array.from_fn n callback state := rfl

theorem residual_claims_exact (claims : Claims) (terminal : Terminal) :
    (install claims terminal).claims = claims := rfl
theorem residual_terminal_exact (claims : Claims) (terminal : Terminal) :
    (install claims terminal).terminal = terminal := rfl

#print axioms coordinates_roundtrip
#print axioms mask_exact
#print axioms root_copy_idempotent
#print axioms circle_installed
#print axioms from_fn_exact
#print axioms residual_claims_exact
#print axioms residual_terminal_exact
end AspisS1FinishChildren
