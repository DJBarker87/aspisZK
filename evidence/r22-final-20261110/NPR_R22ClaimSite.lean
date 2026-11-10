import NPH_R22JoinCW4
import NPH_R22FieldSites

/-! NPR_ (R22, weights.field producer 2): the claim-dot iterator bound. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPR_R22ClaimSite
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim

theorem bind_congr_ok {α β : Type} (m : Result α) (k k' : α → Result β)
    (h : ∀ x, m = ok x → k x = k' x) : (m >>= k) = (m >>= k') := by
  cases m with
  | ok x => simp only [bind_tc_ok]; exact h x rfl
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]

theorem bind_congr_eq {α β : Type} (m m' : Result α) (k k' : α → Result β)
    (hm : m = m') (hk : ∀ x, k x = k' x) : (m >>= k) = (m' >>= k') := by
  rw [hm, show k = k' from funext hk]

/-- Loop congruence on an invariant set closed under continue-steps, with a decreasing measure. -/
theorem loop_congr_inv {α β : Type} (f f' : α → Result (ControlFlow α β)) (S : α → Prop) (μ : α → Nat)
    (hagree : ∀ x, S x → f' x = f x)
    (hstep : ∀ x y, S x → f x = ok (.cont y) → S y ∧ μ y < μ x) :
    ∀ (n : Nat) (x : α), S x → μ x ≤ n → loop f' x = loop f x := by
  intro n
  induction n with
  | zero =>
    intro x hx hn
    rw [Aeneas.Std.loop.eq_def f' x, Aeneas.Std.loop.eq_def f x, hagree x hx]
    cases hfx : f x with
    | ok r =>
      cases r with
      | cont y => have := (hstep x y hx hfx).2; omega
      | done z => rfl
    | fail e => rfl
    | div => rfl
  | succ n ih =>
    intro x hx hn
    rw [Aeneas.Std.loop.eq_def f' x, Aeneas.Std.loop.eq_def f x, hagree x hx]
    cases hfx : f x with
    | ok r =>
      cases r with
      | cont y =>
        have hy := hstep x y hx hfx
        show loop f' y = loop f y
        exact ih y hy.1 (by omega)
      | done z => rfl
    | fail e => rfl
    | div => rfl

variable {D : Type} (ops : ClaimDotOps D)
  (f' : Slice U8 → Usize → Result aspis_core.field.WideExact)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (extra before_z1 : Array aspis_core.field.QM31 29#usize) (y1 : Slice U8)
  (g : Array aspis_core.field.WideExact 29#usize)

theorem inner_body_cont (point : Usize) (iter : core.ops.range.Range Usize) (dot : D)
    (iter1 : core.ops.range.Range Usize) (dot1 : D)
    (run : verifier.borrowed_abi.owned_claim_loops_loop0_loop0.body ops claims extra before_z1 y1 g point iter dot =
      ok (.cont (iter1, dot1))) :
    iter1.end = iter.end ∧ iter1.start.val = iter.start.val + 1 ∧ iter.start.val < iter.end.val := by
  unfold verifier.borrowed_abi.owned_claim_loops_loop0_loop0.body at run
  obtain ⟨⟨o, it⟩, hnext, run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases Result.ok.inj run
  | some l =>
    obtain ⟨_, hend, hs, hlt⟩ := NHI_RangeProgress.some_next iter it l hnext
    obtain ⟨scalar, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨r, next⟩, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨b, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    split at run
    · cases Result.ok.inj run
    · have e := Result.ok.inj run
      cases e
      exact ⟨hend, hs, hlt⟩

/-- One inner (dot) iteration: with iter.end ≤ 29, the field slot is called only at l < 29. -/
theorem inner_body_congr (hagree : ∀ l : Usize, l.val < 29 → f' y1 l = ops.field y1 l)
    (point : Usize) (iter : core.ops.range.Range Usize) (hend : iter.end.val ≤ 29) (dot : D) :
    verifier.borrowed_abi.owned_claim_loops_loop0_loop0.body { ops with field := f' }
        claims extra before_z1 y1 g point iter dot =
      verifier.borrowed_abi.owned_claim_loops_loop0_loop0.body ops claims extra before_z1 y1 g point iter dot := by
  unfold verifier.borrowed_abi.owned_claim_loops_loop0_loop0.body
  refine bind_congr_ok _ _ _ (fun x hx => ?_)
  obtain ⟨o, it⟩ := x
  cases o with
  | none => rfl
  | some l =>
    obtain ⟨hl, _, _, hlt⟩ := NHI_RangeProgress.some_next iter it l hx
    have small : l.val < 29 := by subst hl; omega
    have hs : verifier.borrowed_abi.owned_scalar { ops with field := f' } claims extra before_z1 y1 point l =
        verifier.borrowed_abi.owned_scalar ops claims extra before_z1 y1 point l := by
      unfold verifier.borrowed_abi.owned_scalar
      simp only [hagree l small]
    exact bind_congr_eq _ _ _ _ hs (fun _ => rfl)

theorem inner_congr (hagree : ∀ l : Usize, l.val < 29 → f' y1 l = ops.field y1 l)
    (point : Usize) (dot : D) :
    verifier.borrowed_abi.owned_claim_loops_loop0_loop0 { ops with field := f' }
        { start := 0#usize, «end» := 29#usize } claims extra before_z1 y1 g point dot =
      verifier.borrowed_abi.owned_claim_loops_loop0_loop0 ops
        { start := 0#usize, «end» := 29#usize } claims extra before_z1 y1 g point dot := by
  unfold verifier.borrowed_abi.owned_claim_loops_loop0_loop0
  refine loop_congr_inv _ _ (fun x => x.1.end.val ≤ 29) (fun x => x.1.end.val - x.1.start.val)
    ?_ ?_ 29 _ (by show (29#usize : Usize).val ≤ 29; decide)
    (by show (29#usize : Usize).val - (0#usize : Usize).val ≤ 29; decide)
  · intro x hx
    obtain ⟨it, d⟩ := x
    exact inner_body_congr ops f' claims extra before_z1 y1 g hagree point it hx d
  · intro x y hx hrun
    obtain ⟨it, d⟩ := x
    obtain ⟨it', d'⟩ := y
    have h := inner_body_cont ops claims extra before_z1 y1 g point it d it' d' hrun
    refine ⟨?_, ?_⟩
    · show it'.end.val ≤ 29
      rw [h.1]; exact hx
    · show it'.end.val - it'.start.val < it.end.val - it.start.val
      rw [h.1]; omega

theorem outer_congr (hagree : ∀ l : Usize, l.val < 29 → f' y1 l = ops.field y1 l)
    (iter : core.ops.range.Range Usize) (parts : Array aspis_core.field.WideExact 7#usize) :
    verifier.borrowed_abi.owned_claim_loops_loop0 { ops with field := f' } iter claims extra before_z1 y1 g parts =
      verifier.borrowed_abi.owned_claim_loops_loop0 ops iter claims extra before_z1 y1 g parts := by
  unfold verifier.borrowed_abi.owned_claim_loops_loop0
  congr 1
  funext x
  obtain ⟨it, parts1⟩ := x
  unfold verifier.borrowed_abi.owned_claim_loops_loop0.body
  refine bind_congr_ok _ _ _ (fun y _ => ?_)
  obtain ⟨o, it1⟩ := y
  cases o with
  | none => rfl
  | some point =>
    refine bind_congr_ok _ _ _ (fun dot _ => ?_)
    exact bind_congr_eq _ _ _ _ (inner_congr ops f' claims extra before_z1 y1 g hagree point dot) (fun _ => rfl)

/-- The borrowed owned claim (the deployed claim body, NPH_R22JoinCW5.claim_body) calls its
field slot only at indices l < 29. -/
theorem claim_loops_congr (hagree : ∀ l : Usize, l.val < 29 → f' y1 l = ops.field y1 l)
    (inactive kappa : aspis_core.field.WideExact) :
    verifier.borrowed_abi.owned_claim_loops { ops with field := f' } claims extra before_z1 y1 inactive g kappa =
      verifier.borrowed_abi.owned_claim_loops ops claims extra before_z1 y1 inactive g kappa := by
  unfold verifier.borrowed_abi.owned_claim_loops
  simp only [outer_congr ops f' claims extra before_z1 y1 g hagree]

/-- The guarded form: the claim with its field slot run only at l < 29 equals the claim. -/
theorem claim_guarded (inactive kappa : aspis_core.field.WideExact) :
    verifier.borrowed_abi.owned_claim_loops
        { ops with field := fun y l => if l.val < 29 then ops.field y l else fail .panic }
        claims extra before_z1 y1 inactive g kappa =
      verifier.borrowed_abi.owned_claim_loops ops claims extra before_z1 y1 inactive g kappa :=
  claim_loops_congr ops _ claims extra before_z1 y1 g
    (fun l hl => by simp only [hl, ↓reduceIte]) inactive kappa

/-- claim_site of NPH_R22FieldSites at every index the claim dot reaches. -/
theorem claim_site_reached (l : Usize) (hl : l.val < 29) : NPH_R22FieldSites.Ok3 l :=
  NPH_R22FieldSites.claim_site l (by omega)

#print AspisR1CurrentPreparedClaim.ClaimParser.field
#print axioms loop_congr_inv
#print axioms inner_body_cont
#print axioms inner_body_congr
#print axioms inner_congr
#print axioms outer_congr
#print axioms claim_loops_congr
#print axioms claim_guarded
#print axioms claim_site_reached
end AspisR1.NPR_R22ClaimSite
