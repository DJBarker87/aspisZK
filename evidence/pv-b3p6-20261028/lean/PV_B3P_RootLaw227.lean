import PV_B3P_P227_14
import PV_B3P_SelectValue227
import PV_B3P_FieldExt227
namespace PV_B3P_RootLaw227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev Claims := PV_B3P_SelectIndex227.Claims
abbrev Point := Array Q 10#usize
abbrev Public := reference_terminal.SemanticPublic
abbrev Challenges := aspis_core.state_only_prefix.r0.Challenges

def selected (claims : Claims) : Array Q 84#usize :=
  ⟨PV_B3P_SelectValue227.expected claims,PV_B3P_SelectValue227.expected_length claims⟩

theorem selected_result (claims : Claims) :
    reference_terminal.select227 claims=.ok (selected claims) := by
  obtain ⟨out,hout,hval⟩ := PV_B3P_SelectValue227.nonvacuity claims
  have he : out=selected claims := Subtype.ext hval
  rw [hout,he]

/-- The final ordered field combination; no reassociation is used. -/
def combination (composition h1_z copy_active equality mu : Q) : Q :=
  let q1 := PV_B3P_FieldExt227.qmul equality composition
  let q2 := PV_B3P_FieldExt227.qmul mu h1_z
  let q3 := PV_B3P_FieldExt227.qadd q1 q2
  let q4 := PV_B3P_FieldExt227.qmul mu mu
  let q5 := PV_B3P_FieldExt227.qsub aspis_core.field.QM31.ONE copy_active
  let q6 := PV_B3P_FieldExt227.qmul q5 h1_z
  let q7 := PV_B3P_FieldExt227.qmul q4 q6
  PV_B3P_FieldExt227.qadd q3 q7

/-- A complete Result plan for selection, composition, equality and the final
field combination. Composition and equality remain the closed emitted bodies;
this theorem alone does not provide their native structural correspondence or
successful nonvacuity. -/
def plan (p : Public) (claims : Claims) (point : Point) (c : Challenges) :
    Result (core.result.Result Q aspis_core.state_only_prefix.r0.Error) := do
  let result ← reference_terminal.composition_parts p (selected claims) point c.lambda c.chi c.theta
  match result with
  | .Err _ => .ok (.Err aspis_core.state_only_prefix.r0.Error.Public)
  | .Ok (composition,_,_,_,h1_z,copy_active) =>
    let equality ← reference_terminal.equality_value c.zc point
    .ok (.Ok (combination composition h1_z copy_active equality c.mu))

theorem complete_result (p : Public) (claims : Claims) (point : Point) (c : Challenges) :
    reference_terminal.reference227 p claims point c=plan p claims point c := by
  unfold reference_terminal.reference227
  rw [selected_result]
  simp only [bind_tc_ok]
  unfold reference_terminal.terminal_parts plan
  cases hc : reference_terminal.composition_parts p (selected claims) point c.lambda c.chi c.theta with
  | fail e => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err e => rfl
    | Ok parts =>
      rcases parts with ⟨composition,c1,mask,g,h1_z,copy_active⟩
      cases he : reference_terminal.equality_value c.zc point with
      | fail e => rfl
      | div => rfl
      | ok equality =>
        simp only [bind_tc_ok,PV_B3P_FieldExt227.qmul_result,
          PV_B3P_FieldExt227.qadd_result,PV_B3P_FieldExt227.qsub_result,combination]

#print axioms selected_result
#print axioms complete_result
end PV_B3P_RootLaw227
