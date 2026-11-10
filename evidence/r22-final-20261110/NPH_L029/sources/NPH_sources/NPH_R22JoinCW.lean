import NPH_R22Callbacks
import CurrentFinishField
import CurrentClaimSumModel
import RPz7_FIn_ExtractInstall
import SAG_StageScale

/-! NPH_ (R22, run of 2026-11-10 evening, step B): CurrentWide (CW) sites outside the 094
query path. W is limbs ≤ P (NPH_R22Weak); WE/CWW are W on the Stage2 and CW wide carriers
(NPH_R22Callbacks).
- Producer: every successful FIn_Primitives.field read is W (AspisR1CurrentWide.Proof.
  finishField_success_canonical, through the field-wise copy toStageE).
- Wrapper W-lemmas: FIn_Primitives.add, FIn_Polynomial.mul, AspisR1CurrentWide.Proof.finishAdd,
  and the CurrentClaimSumModel copies AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add
  and .mul: W inputs give an ok W output (every CW kernel call inside receives W arguments).
- Site join, the extracted Horner FIn_Extract.FIn_reference.polynomial on
  FIn_ExtractInstall.arithmetic: each multiply takes the accumulator (zero, or an earlier ok
  output) and x; each add takes that product and a successful field read. For a W point x,
  every step is ok with W output (`poly_steps`), and when all seven reads succeed the whole
  polynomial is ok and W (`poly_W`).
- Site join, the Stage2 round finishRelationRoundWithOps on any FinishOps whose field/add/
  mulM/polynomial slots are the deployed ones (the slots of IDa_Deployed.finish, by rfl):
  `lhs ← add (field poly 0) (field poly 4)` is ok and W on successful reads, `mulM claim m`
  is ok for every claim and m (mul_m31 is total), and the polynomial step is the join above
  for a W alpha. The alpha argument is p.alpha[0] or p.alpha[1] of the finish Prepared value;
  its W bound is NOT proved here (an open context).
Standard axioms; no ops interface, merged module or closed-row statement is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22JoinCW
open Aeneas Aeneas.Std Result AspisR1.NPH_R22Producers AspisR1.NPH_R22Callbacks

theorem canonWide_W (x : AspisR1CurrentWide.field.wide_exact.WideExact)
    (h : AspisR1CurrentWide.Proof.CanonicalWide x) : CWW x := by
  obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩⟩ := h
  exact ⟨⟨⟨Nat.le_of_lt h1, Nat.le_of_lt h2⟩, ⟨Nat.le_of_lt h3, Nat.le_of_lt h4⟩⟩,
    ⟨⟨Nat.le_of_lt h5, Nat.le_of_lt h6⟩, ⟨Nat.le_of_lt h7, Nat.le_of_lt h8⟩⟩⟩

/-- Producer: a successful finish field read is W. -/
theorem FIn_field_W (bytes : Slice U8) (i : Usize) (v : SAQ_WideABI.E)
    (h : AspisR1.FIn_Primitives.field bytes i = ok v) : WE v := by
  unfold AspisR1.FIn_Primitives.field at h
  obtain ⟨x, hx, he⟩ := Port3_PushFrame.bind_success _ _ _ h
  have hv : AspisR1.SAG_DotAdapter.toStageE x = v := Result.ok.inj he
  subst hv
  exact canonWide_W _ (AspisR1CurrentWide.Proof.finishField_success_canonical bytes i x hx)

theorem FIn_add_W (x y : SAQ_WideABI.E) (hx : WE x) (hy : WE y) :
    ∃ z, AspisR1.FIn_Primitives.add x y = ok z ∧ WE z := by
  obtain ⟨w, hw, vw⟩ := CW_WideExact_add_weak (SAQ_WideABI.toW x) (SAQ_WideABI.toW y) hx hy
  exact ⟨SAQ_WideABI.fromW w, by simp only [AspisR1.FIn_Primitives.add, hw, bind_tc_ok], vw⟩

theorem FIn_mul_W (x y : SAQ_WideABI.E) (hx : WE x) (hy : WE y) :
    ∃ z, AspisR1.FIn_Polynomial.mul x y = ok z ∧ WE z := by
  obtain ⟨w, hw, vw⟩ := CW_WideExact_mul_weak (SAQ_WideABI.toW x) (SAQ_WideABI.toW y) hx hy
  exact ⟨SAQ_WideABI.fromW w, by simp only [AspisR1.FIn_Polynomial.mul, hw, bind_tc_ok], vw⟩

theorem FIn_zero_W : WE AspisR1.FIn_Polynomial.zero :=
  ⟨⟨⟨zero_W, zero_W⟩, ⟨zero_W, zero_W⟩⟩, ⟨⟨zero_W, zero_W⟩, ⟨zero_W, zero_W⟩⟩⟩

/-- One Horner step at the deployed arithmetic: from a W accumulator and a W point, the
multiply is ok and W, and on a successful read the add is ok and W. -/
theorem poly_step (bytes : Slice U8) (i : Usize) (a x : SAQ_WideABI.E) (ha : WE a) (hx : WE x) :
    ∃ t, AspisR1.FIn_ExtractInstall.arithmetic.mul a x = ok t ∧ WE t ∧
      ∀ c, AspisR1.FIn_ExtractInstall.arithmetic.field bytes i = ok c →
        ∃ a', AspisR1.FIn_ExtractInstall.arithmetic.add t c = ok a' ∧ WE a' := by
  obtain ⟨t, ht, wt⟩ := FIn_mul_W a x ha hx
  refine ⟨t, ht, wt, fun c hc => ?_⟩
  exact FIn_add_W t c wt (FIn_field_W bytes i c hc)

theorem poly_W (bytes : Slice U8) (x : SAQ_WideABI.E) (hx : WE x)
    (hr : ∀ i : Usize, ∃ v, AspisR1.FIn_Primitives.field bytes i = ok v) :
    ∃ z, AspisR1.FIn_ExtractInstall.polynomial bytes x = ok z ∧ WE z := by
  obtain ⟨t1, h1, w1⟩ := FIn_mul_W _ x FIn_zero_W hx
  obtain ⟨r6, g6⟩ := hr 6#usize
  obtain ⟨a6, k6, v6⟩ := FIn_add_W t1 r6 w1 (FIn_field_W _ _ _ g6)
  obtain ⟨t3, h3, w3⟩ := FIn_mul_W a6 x v6 hx
  obtain ⟨r5, g5⟩ := hr 5#usize
  obtain ⟨a5, k5, v5⟩ := FIn_add_W t3 r5 w3 (FIn_field_W _ _ _ g5)
  obtain ⟨t5, h5, w5⟩ := FIn_mul_W a5 x v5 hx
  obtain ⟨r4, g4⟩ := hr 4#usize
  obtain ⟨a4, k4, v4⟩ := FIn_add_W t5 r4 w5 (FIn_field_W _ _ _ g4)
  obtain ⟨t7, h7, w7⟩ := FIn_mul_W a4 x v4 hx
  obtain ⟨r3, g3⟩ := hr 3#usize
  obtain ⟨a3, k3, v3⟩ := FIn_add_W t7 r3 w7 (FIn_field_W _ _ _ g3)
  obtain ⟨t9, h9, w9⟩ := FIn_mul_W a3 x v3 hx
  obtain ⟨r2, g2⟩ := hr 2#usize
  obtain ⟨a2, k2, v2⟩ := FIn_add_W t9 r2 w9 (FIn_field_W _ _ _ g2)
  obtain ⟨t11, h11, w11⟩ := FIn_mul_W a2 x v2 hx
  obtain ⟨r1, g1⟩ := hr 1#usize
  obtain ⟨a1, k1, v1⟩ := FIn_add_W t11 r1 w11 (FIn_field_W _ _ _ g1)
  obtain ⟨t13, h13, w13⟩ := FIn_mul_W a1 x v1 hx
  obtain ⟨r0, g0⟩ := hr 0#usize
  obtain ⟨a0, k0, v0⟩ := FIn_add_W t13 r0 w13 (FIn_field_W _ _ _ g0)
  refine ⟨a0, ?_, v0⟩
  simp only [AspisR1.FIn_ExtractInstall.polynomial, FIn_Extract.FIn_reference.polynomial,
    AspisR1.FIn_ExtractInstall.arithmetic, h1, g6, k6, h3, g5, k5, h5, g4, k4, h7, g3, k3,
    h9, g2, k2, h11, g1, k1, h13, g0, k0, bind_tc_ok]

/-- The Stage2 finish round at the deployed slots. -/
theorem round_sites {W : Type} (ops : AspisR1Stage2.Stage2Finish.FinishOps W)
    (hf : ops.field = AspisR1.FIn_Primitives.field) (ha : ops.add = AspisR1.FIn_Primitives.add)
    (hm : ops.mulM = AspisR1.SAG_StageScale.mulM)
    (hp : ops.polynomial = AspisR1.FIn_ExtractInstall.polynomial)
    (poly : Slice U8) (alpha claim : SAQ_WideABI.E) :
    (∀ we we1, ops.field poly 0#usize = ok we → ops.field poly 4#usize = ok we1 →
      ∃ lhs, ops.add we we1 = ok lhs ∧ WE lhs) ∧
    (∀ m, ∃ rhs, ops.mulM claim m = ok rhs) ∧
    (WE alpha → (∀ i : Usize, ∃ v, ops.field poly i = ok v) →
      ∃ z, ops.polynomial poly alpha = ok z ∧ WE z) := by
  refine ⟨fun we we1 h0 h4 => ?_, fun m => ?_, fun hα hr => ?_⟩
  · rw [hf] at h0 h4; rw [ha]
    exact FIn_add_W we we1 (FIn_field_W _ _ _ h0) (FIn_field_W _ _ _ h4)
  · rw [hm]
    obtain ⟨w, hw, _⟩ := CW_WideExact_mul_m31_weak (SAQ_WideABI.toW claim) m
    exact ⟨SAQ_WideABI.fromW w, by simp only [AspisR1.SAG_StageScale.mulM, hw, bind_tc_ok]⟩
  · rw [hf] at hr; rw [hp]
    exact poly_W poly alpha hα hr

theorem finishAdd_W (x y : AspisR1CurrentWide.Proof.FinishE)
    (hx : CWW (AspisR1CurrentWide.Proof.ofFinishE x)) (hy : CWW (AspisR1CurrentWide.Proof.ofFinishE y)) :
    ∃ z, AspisR1CurrentWide.Proof.finishAdd x y = ok z ∧ CWW (AspisR1CurrentWide.Proof.ofFinishE z) := by
  obtain ⟨w, hw, vw⟩ := CW_WideExact_add_weak _ _ hx hy
  exact ⟨AspisR1CurrentWide.Proof.toFinishE w,
    by simp only [AspisR1CurrentWide.Proof.finishAdd, hw, bind_tc_ok], vw⟩

theorem claimAdd_W (x y : AspisR1CurrentPreparedClaim.Concrete.E)
    (hx : CWW (AspisR1CurrentPreparedClaim.Concrete.toFull x))
    (hy : CWW (AspisR1CurrentPreparedClaim.Concrete.toFull y)) :
    ∃ z, AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add x y = ok z ∧
      CWW (AspisR1CurrentPreparedClaim.Concrete.toFull z) := by
  obtain ⟨w, hw, vw⟩ := CW_WideExact_add_weak _ _ hx hy
  refine ⟨AspisR1CurrentPreparedClaim.Concrete.fromFull w,
    by simp only [AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add, hw, bind_tc_ok], ?_⟩
  rw [AspisR1CurrentPreparedClaim.Concrete.to_from]; exact vw

theorem claimMul_W (x y : AspisR1CurrentPreparedClaim.Concrete.E)
    (hx : CWW (AspisR1CurrentPreparedClaim.Concrete.toFull x))
    (hy : CWW (AspisR1CurrentPreparedClaim.Concrete.toFull y)) :
    ∃ z, AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.mul x y = ok z ∧
      CWW (AspisR1CurrentPreparedClaim.Concrete.toFull z) := by
  obtain ⟨w, hw, vw⟩ := CW_WideExact_mul_weak _ _ hx hy
  refine ⟨AspisR1CurrentPreparedClaim.Concrete.fromFull w,
    by simp only [AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.mul, hw, bind_tc_ok], ?_⟩
  rw [AspisR1CurrentPreparedClaim.Concrete.to_from]; exact vw

#print axioms canonWide_W
#print axioms FIn_field_W
#print axioms FIn_add_W
#print axioms FIn_mul_W
#print axioms FIn_zero_W
#print axioms poly_step
#print axioms poly_W
#print axioms round_sites
#print axioms finishAdd_W
#print axioms claimAdd_W
#print axioms claimMul_W
end AspisR1.NPH_R22JoinCW
