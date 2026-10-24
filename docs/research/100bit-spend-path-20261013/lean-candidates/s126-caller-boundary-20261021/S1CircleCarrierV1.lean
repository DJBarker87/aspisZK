import S1SemanticAlphaV1
import S9CircleWrapperOutputCanonicalV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1CircleCarrier
open Aeneas Aeneas.Std Result
abbrev K := aspis_core.field.QM31
abbrev Point := aspis_core.circle.SecureCirclePoint
abbrev WK := AspisR1CircleSampleWrapper.field.QM31
abbrev WPoint := AspisR1CircleSampleWrapper.circle.SecureCirclePoint

def toK (q : WK) : K := {c0:={a:=q.c0.a,b:=q.c0.b},c1:={a:=q.c1.a,b:=q.c1.b}}
def fromK (q : K) : WK := {c0:={a:=q.c0.a,b:=q.c0.b},c1:={a:=q.c1.a,b:=q.c1.b}}
def toPoint (p : WPoint) : Point := {x:=toK p.x,y:=toK p.y}
def fromPoint (p : Point) : WPoint := {x:=fromK p.x,y:=fromK p.y}
@[simp] theorem k_round (q : WK) : fromK (toK q)=q := rfl
@[simp] theorem k_back (q : K) : toK (fromK q)=q := rfl
@[simp] theorem point_round (p : WPoint) : fromPoint (toPoint p)=p := rfl
@[simp] theorem point_back (p : Point) : toPoint (fromPoint p)=p := rfl

def row : FinishModel.CircleRow → AspisR1CircleSampleWrapper.r0_transcript.CircleRow
  | .First => .First | .Second => .Second

/-- Retained emitted circle wrapper, with all coordinate words and the actual
row preserved. Its native current callee association remains S9's open gate. -/
def circle (block : Array U8 32#usize) (r : FinishModel.CircleRow) : Result Point := do
  let p ← AspisR1CircleSampleWrapper.sampler.circle_sample block (row r)
  ok (toPoint p)

def Canonical (q : K) : Prop :=
  (q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647) ∧
  (q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647)

/-- Reuse S9's proved wrapper fact on THIS returned point. No separate sampler
success, point choice or canonical-coordinate hypothesis remains. -/
theorem circle_canonical (block : Array U8 32#usize) (r : FinishModel.CircleRow) (p : Point)
    (success : circle block r=ok p) : Canonical p.x ∧ Canonical p.y := by
  unfold circle at success
  cases call : AspisR1CircleSampleWrapper.sampler.circle_sample block (row r) with
  | fail error => simp only [call,bind_tc_fail] at success;cases success
  | div => simp only [call,bind_tc_div] at success;cases success
  | ok out =>
    simp only [call,bind_tc_ok] at success
    have same : toPoint out=p := Result.ok.inj success
    rw [←same]
    have canonical := AspisR1S9CircleWrapperOutputCanonicalV1.successful_wrapper_circle_coordinates_canonical
      block (row r) out call
    rcases canonical with ⟨⟨h0,h1,h2,h3⟩,⟨h4,h5,h6,h7⟩⟩
    exact ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩

#print axioms point_round
#print axioms point_back
#print axioms circle_canonical
end AspisR1PublicPreparation.S1CircleCarrier
