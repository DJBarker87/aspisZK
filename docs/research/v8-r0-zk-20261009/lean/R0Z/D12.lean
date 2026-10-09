import R0Z.JointTrace
import R0Z.AbsorptionLaw

/-! D12 for the current honest joint-tape experiment. A retains all linear
mask observations and all non-round observations. The original terminal's
entire change (including any linear terms) is assigned to g. This explicit
choice makes A common to all instances and g(0)=0 without choosing a
witness-dependent derivative or assuming any new premise. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.D12
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

abbrev HonestProver := JointView.HonestProver
abbrev HonestInstance := @JointView.HonestInstance
abbrev Statement := JointView.Statement

def payload (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (t : T K F) : Payload K :=
  JointView.payload h B x w ch (Partition.equiv t)

abbrev c := @JointView.c

def A (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) : T K F →ₗ[F] Payload K :=
  ((PayloadSplit.L π B ch).restrictScalars F).comp (JointTrace.tapeLinear B)

abbrev roundInclusion : PayloadSplit.RoundPayload K →ₗ[F] Payload K :=
  PayloadSplit.roundInclusion.restrictScalars F

def g (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (n : N K F) : PayloadSplit.RoundPayload K :=
  PayloadSplit.originalRounds x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch (0,n)) -
    PayloadSplit.originalRounds x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch 0)

theorem g_zero (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) : g h B x w ch 0 = 0 := sub_self _

/-- D12's pure common slope, for every payload component, every n and every w. -/
theorem M_pure (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (m : M K F) (n : N K F) :
    payload h B x w ch (m,n) = payload h B x w ch (0,n) +
      (A h.transport B ch).comp inlM m := by
  have ha : (A h.transport B ch).comp inlM m = PayloadSplit.pureLinear h.transport B ch m := by
    change PayloadSplit.L h.transport B ch (JointTrace.tapeLinear B (m,0)) = _
    rw [JointTrace.tapeLinear_pure]
    rfl
  rw [ha]
  exact PayloadSplit.M_pure h.transport x.1 B (h.build w) ch m n

/-- The zero-tape payload is the existing JointView.c, and the remainder
has support only in the ten round-polynomial arrays. -/
theorem decomposition (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (t : T K F) :
    payload h B x w ch t = c h B x w ch + A h.transport B ch t + roundInclusion (F := F) (g h B x w ch t.2) := by
  let u := PayloadSplit.actual x.1 B (h.build w) ch
  have hs (r : T K F) : payload h B x w ch r =
      PayloadSplit.L h.transport B ch (u r) + PayloadSplit.O x.1 B ch (u r) :=
    PayloadSplit.run_split h.transport x.1 B (applyEligible (h.build w) r.2.2) ch (aff r)
  have hz : payload h B x w ch 0 = c h B x w ch :=
    congrArg (JointView.payload h B x w ch) (map_zero Partition.equiv)
  have hc : c h B x w ch = PayloadSplit.L h.transport B ch (u 0) + PayloadSplit.O x.1 B ch (u 0) :=
    hz.symm.trans (hs 0)
  have hl : PayloadSplit.L h.transport B ch (u t) = PayloadSplit.L h.transport B ch (u 0) + A h.transport B ch t := by
    dsimp only [u]
    rw [JointTrace.actual_affine, map_add]
    rfl
  have ho : PayloadSplit.O x.1 B ch (u t) = PayloadSplit.O x.1 B ch (u (0,t.2)) := by
    dsimp only [u]
    rw [PayloadSplit.actual_add_pure, PayloadSplit.O_add_pure]
  have hg : roundInclusion (F := F) (g h B x w ch t.2) =
      PayloadSplit.O x.1 B ch (u (0,t.2)) - PayloadSplit.O x.1 B ch (u 0) := by
    exact map_sub PayloadSplit.roundInclusion _ _
  rw [hs, hl, ho, hc, hg]
  abel

/-- Zero the round arrays and retain every other payload coordinate. -/
def nonRound : Payload K →ₗ[F] Payload K :=
  LinearMap.pi fun coord => match coord with
  | .semanticCoeff _ _ => 0
  | coord => (LinearMap.proj coord : Payload K →ₗ[F] K)

theorem nonRound_roundInclusion (p : PayloadSplit.RoundPayload K) :
    nonRound (F := F) (roundInclusion (F := F) p) = 0 := by
  funext coord
  cases coord <;> rfl

/-- All other disclosed components are jointly affine in (m,n), with the
same coefficients for every instance. -/
theorem other_components_affine (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K) (t : T K F) :
    nonRound (F := F) (payload h B x w ch t) = nonRound (F := F) (c h B x w ch) +
      nonRound (F := F) (A h.transport B ch t) := by
  rw [decomposition, map_add, map_add, nonRound_roundInclusion, add_zero]

/-- D12 verbatim, with the universally fixed challenge made explicit and
(g,0) written as its round-only inclusion. There is no range-equality,
helper-invariance, affinity, validity or rank premise hidden here. -/
def MaskImage (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle) : Prop :=
  (∀ ch w n, h.public w = x.1 →
    roundInclusion (F := F) (g h B x w ch n) ∈ LinearMap.range ((A h.transport B ch).comp inlM)) ∧
  (∀ ch w w', h.public w = x.1 → h.public w' = x.1 →
    c h B x w ch - c h B x w' ch ∈ LinearMap.range (A h.transport B ch))

theorem payload_law (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) (hm : MaskImage h B x)
    (w : h.Instance) (ch : Challenges K) (hw : h.public w = x.1) :
    EqualLaws (payload h B x w ch) (fun t => c h B x w ch + A h.transport B ch t) := by
  have hh := AbsorptionLaw.mixture (A h.transport B ch) (c h B x w ch)
    (fun n => roundInclusion (F := F) (g h B x w ch n)) (fun n => hm.1 ch w n hw)
  intro v
  simpa only [← decomposition] using hh v

attribute [local irreducible] JointView.payload A g

/-- D12: fixed-N cosets, their uniform mixture, then the common coset from
(ii). Transport the coordinate permutation back to the unchanged experiment. -/
theorem hvzk_perfect_of_maskImage (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) : MaskImage h B x → JointView.HVZK_perfect h B outputs x := by
  intro hm hx w ch hw
  let w' := Classical.choose hx
  have hw' : h.public w' = x.1 := Classical.choose_spec hx
  have hlinear := AffineLaw.equal_laws_of_mask_image (A h.transport B ch) (A h.transport B ch)
    (c h B x w ch) (c h B x w' ch) rfl (hm.2 ch w w' hw hw')
  have hpart : EqualLaws (payload h B x w ch) (payload h B x w' ch) := by
    intro v
    exact (payload_law h B x hm w ch hw v).trans
      ((hlinear v).trans (payload_law h B x hm w' ch hw' v).symm)
  have hold : EqualLaws (JointView.payload h B x w ch) (JointView.payload h B x w' ch) := by
    apply AbsorptionLaw.equal_laws_of_equiv Partition.equiv.toEquiv
    unfold payload at hpart
    exact hpart
  have hp := AffineLaw.equal_laws_const_pair (JointView.payload h B x w ch)
    (JointView.payload h B x w' ch) (ZkStatement.metadata outputs x ch) hold
  unfold JointView.simulator JointView.view
  dsimp only [w'] at hp
  exact hp

#print MaskImage
#print axioms M_pure
#print axioms decomposition
#print axioms g_zero
#print axioms other_components_affine
#print axioms hvzk_perfect_of_maskImage
end R0Z.D12
