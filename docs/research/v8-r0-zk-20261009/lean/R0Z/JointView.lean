import R0Z.ZkStatement

/-! D11's joint uniform tape and current privacy experiment. The binary
direct sum of the two vector spaces is represented by their product, with
LinearMap.inl/inr as its injections; it is not a choice of one summand.
No affine decomposition or image hypothesis is installed in this interface. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.JointView
open R0P R0Z.MaskLayout
attribute [local instance] Classical.propDecidable

abbrev HonestProver := ZkStatement.HonestProver
abbrev HonestInstance {K : Type} (h : HonestProver K) := h.Instance
abbrev Statement := ZkStatement.Statement
abbrev Challenges := HonestView.Challenges
abbrev View := ZkStatement.View
abbrev Payload := HonestView.Payload

abbrev Tape (K : Type) [Field K] (F : Subfield K) :=
  AffTape K F × EligibleNoise K F

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

def payload (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : HonestInstance h) (ch : Challenges K) (t : Tape K F) : Payload K :=
  HonestView.run h.transport x.1 B (applyEligible (h.build w) t.2) ch t.1

def view (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : HonestInstance h) (ch : Challenges K)
    (t : Tape K F) : View K CommitHandle Aux :=
  (ZkStatement.metadata outputs x ch, payload h B x w ch t)

def c (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : HonestInstance h) (ch : Challenges K) : Payload K :=
  payload h B x w ch (0, 0)

def InLanguage (h : HonestProver K) (x : Statement K CommitHandle) : Prop :=
  ∃ w : HonestInstance h, h.public w = x.1

/-- Choose only an instance for the public statement. Both noise tapes are
sampled by the simulator, just as in the honest joint-tape experiment. -/
def simulator (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hx : InLanguage h x) (ch : Challenges K) :
    Tape K F → View K CommitHandle Aux :=
  view h B outputs x (Classical.choose hx) ch

def HVZK_perfect (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) : Prop :=
  ∀ (hx : InLanguage h x) (w : HonestInstance h) ch, h.public w = x.1 →
    EqualLaws (view h B outputs x w ch) (simulator h B outputs x hx ch)

/-- Exact correspondence with the accepted Z3 view; only the location of
eligible noise in the experiment changes. -/
theorem view_eq_z3 (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : HonestInstance h) (ch : Challenges K)
    (r : AffTape K F) (e : EligibleNoise K F) :
    view h B outputs x w ch (r,e) = ZkStatement.view h B outputs x (w,e) ch r := rfl

#print axioms view_eq_z3
#print axioms HVZK_perfect
end R0Z.JointView
