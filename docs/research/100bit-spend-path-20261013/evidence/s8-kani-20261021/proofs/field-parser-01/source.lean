import S8OwnedP6.Funs
import R1CandidateFieldParsers

set_option autoImplicit false
namespace AspisR1.S8OwnedP6FieldParserTransport
open Aeneas Aeneas.Std Result

abbrev ActualC := S8OwnedP6.aspis_core.field.CM31
abbrev ActualQ := S8OwnedP6.aspis_core.field.QM31
abbrev CandidateC := AspisR1CandidateParser.field.CM31
abbrev CandidateQ := AspisR1CandidateParser.field.QM31

def cToCandidate (x : ActualC) : CandidateC := ⟨x.a,x.b⟩
def qToCandidate (x : ActualQ) : CandidateQ := ⟨cToCandidate x.c0,cToCandidate x.c1⟩

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem mapResult_bind {A B C : Type} (f : B → C) (r : Result A) (k : A → Result B) :
    mapResult f (r >>= k) = r >>= fun a => mapResult f (k a) := by
  cases r <;> rfl

theorem mapResult_match_core {A B C D : Type} (f : C → D)
    (r : core.result.Result A B) (ok : A → Result C) (err : B → Result C) :
    mapResult f (match r with | .Ok a => ok a | .Err b => err b) =
      match r with | .Ok a => mapResult f (ok a) | .Err b => mapResult f (err b) := by
  cases r <;> rfl

theorem mapResult_match_flow {A B C D : Type} (f : C → D)
    (r : core.ops.control_flow.ControlFlow A B) (br : A → Result C) (ct : B → Result C) :
    mapResult f (match r with | .Break a => br a | .Continue b => ct b) =
      match r with | .Break a => mapResult f (br a) | .Continue b => mapResult f (ct b) := by
  cases r <;> rfl

theorem modulus_eq : S8OwnedP6.aspis_core.field.P = AspisR1CandidateParser.field.P := by
  unfold S8OwnedP6.aspis_core.field.P AspisR1CandidateParser.field.P
  rfl

theorem m31_parser_eq (bytes : Array U8 4#usize) :
    S8OwnedP6.aspis_core.field.M31.from_le_bytes bytes =
      AspisR1CandidateParser.field.M31.from_le_bytes bytes := by
  unfold S8OwnedP6.aspis_core.field.M31.from_le_bytes
    AspisR1CandidateParser.field.M31.from_le_bytes
  rw [modulus_eq]

theorem residual_c_eq (o : Option core.convert.Infallible) :
    mapResult (Option.map cToCandidate)
      (S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual ActualC o) =
      AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual CandidateC o := by
  cases o with
  | none => rfl
  | some impossible => cases impossible

theorem bind_congr_right {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) := by
  cases r with
  | ok a => exact h a
  | fail e => rfl
  | div => rfl

theorem cm_parser_eq (bytes : Slice U8) :
    mapResult (Option.map cToCandidate)
      (S8OwnedP6.aspis_core.field.CM31.from_le_bytes bytes) =
      AspisR1CandidateParser.field.CM31.from_le_bytes bytes := by
  unfold S8OwnedP6.aspis_core.field.CM31.from_le_bytes
    AspisR1CandidateParser.field.CM31.from_le_bytes
  simp only [mapResult_bind]
  apply bind_congr_right
  intro slice0
  apply bind_congr_right
  intro array0
  cases array0 with
  | Err e => rfl
  | Ok value0 =>
    simp only [m31_parser_eq, mapResult_bind]
    apply bind_congr_right
    intro opt0
    cases opt0 with
    | none =>
      simp only [S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_tc_ok]
      exact residual_c_eq none
    | some limb0 =>
      simp only [S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_tc_ok,
        mapResult_bind]
      apply bind_congr_right
      intro slice1
      apply bind_congr_right
      intro array1
      cases array1 with
      | Err e => rfl
      | Ok value1 =>
        simp only [m31_parser_eq, mapResult_bind]
        apply bind_congr_right
        intro opt1
        cases opt1 with
        | none =>
          simp only [S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_tc_ok]
          exact residual_c_eq none
        | some limb1 =>
          simp only [S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_tc_ok]
          rfl

#print axioms modulus_eq
#print axioms m31_parser_eq
#print axioms residual_c_eq
#print axioms cm_parser_eq
#print axioms mapResult_bind
#print axioms mapResult_match_core
#print axioms mapResult_match_flow
#print axioms bind_congr_right

end AspisR1.S8OwnedP6FieldParserTransport
