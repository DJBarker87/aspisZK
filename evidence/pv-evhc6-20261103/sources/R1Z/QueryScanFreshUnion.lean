import R1Z.QueryScanRealEntropy

/-! Scan-step/earlier-entry union bound with a conservative 190-bit exponent.
Each pair law is proved using the retained real/lazy coupling, not inferred
from marginal entropy alone. The marginal state entropy is proved separately. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanFreshUnion
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV
  R0Z.FsAbortBounds R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin
  R1Z.EventsR1PBin R1Z.TranscriptR1 R1Z.AgreeR1PBin R1Z.LazyFrozen
  R1Z.QueryScanFreshInputs R1Z.QueryScanRealLazyBound R1Z.QueryScanRealFreshMass
  R1Z.QueryScanRealEntropy
attribute [local instance] Classical.propDecidable

def scanRead (j : Fin 8) : Bool → TRead
  | false => .qb j
  | true => .qa j

def freshBudget (q : ℕ) : ℚ := 128 * (q : ℚ) / (2 : ℚ)^190

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (R : RomModel W) (N : ℕ) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (w : h.Instance)

abbrev ScanStep := Fin N × Fin 8 × Bool

def scanIndex (p : ScanStep N) : Fin (N * n1 W Pr) :=
  (posE W Pr N).symm (p.1, .inl (scanRead p.2.1 p.2.2))

theorem scan_index_coverage (i : Fin (N * n1 W Pr)) (hi : scanPosition W Pr N i) :
    ∃ p, scanIndex W Pr N p = i := by
  rcases hp : posE W Pr N i with ⟨k, j | c⟩
  · cases j with
    | qb j =>
        refine ⟨(k,j,false), ?_⟩
        apply (posE W Pr N).injective
        simpa only [scanIndex, Equiv.apply_symm_apply, scanRead] using hp.symm
    | qa j =>
        refine ⟨(k,j,true), ?_⟩
        apply (posE W Pr N).injective
        simpa only [scanIndex, Equiv.apply_symm_apply, scanRead] using hp.symm
    | _ => simp [scanPosition, hp, IsScan] at hi
  · simp [scanPosition, hp] at hi

def issued (r : W.Tab × (Fin N → SecP)) (i : Fin (N * n1 W Pr)) : List UInt8 :=
  let a := gAddr W Pr h B outputs x w r.2 (W.look r.1 (W.pubBytes x))
  a i (runN a (W.look r.1) 0 i.val)

def priorHit (p : ScanStep N) (earlier : Option (Fin (N * n1 W Pr)))
    (r : W.Tab × (Fin N → SecP)) : Prop :=
  match earlier with
  | none => issued W Pr N h B outputs x w r (scanIndex W Pr N p) = W.pubBytes x
  | some j => j < scanIndex W Pr N p ∧
      issued W Pr N h B outputs x w r j = issued W Pr N h B outputs x w r (scanIndex W Pr N p)

theorem fresh_iff_prior_hit (r : W.Tab × (Fin N → SecP)) :
    realFresh W Pr N h B outputs x w r ↔
      ∃ p earlier, priorHit W Pr N h B outputs x w p earlier r := by
  constructor
  · rintro ⟨i, hi, he | ⟨j, hj, he⟩⟩
    · obtain ⟨p, rfl⟩ := scan_index_coverage W Pr N i hi
      exact ⟨p, none, he⟩
    · obtain ⟨p, rfl⟩ := scan_index_coverage W Pr N i hi
      exact ⟨p, some j, hj, he⟩
  · rintro ⟨p, earlier, he⟩
    have hi : scanPosition W Pr N (scanIndex W Pr N p) := by
      simp only [scanPosition, scanIndex, Equiv.apply_symm_apply]
      cases p.2.2 <;> trivial
    refine ⟨scanIndex W Pr N p, hi, ?_⟩
    cases earlier with
    | none => exact Or.inl he
    | some j => exact Or.inr ⟨j, he⟩

include hN in
/-- Individual earlier-entry guessing law, valid on actual real randomness.
A stronger 204-bit envelope pays upstream collisions before this pair. -/
theorem prior_hit_mass (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w) (hb : RCommitBytes W Pr)
    (hE₁ : Pr.E₁ ≤ 2^64) (hE₂ : Pr.E₂ ≤ 2^64)
    (hM : N * n1 W Pr ≤ 2^25) (p : ScanStep N)
    (earlier : Option (Fin (N * n1 W Pr))) :
    eventMass (priorHit W Pr N h B outputs x w p earlier) ≤ 1 / (2 : ℚ)^190 := by
  have hs := eventMass_mono (priorHit W Pr N h B outputs x w p earlier)
    (realFresh W Pr N h B outputs x w)
    (fun r hr => (fresh_iff_prior_hit W Pr N h B outputs x w r).mpr ⟨p, earlier, hr⟩)
  exact (hs.trans (real_fresh_mass W Pr R N hN h B outputs x w hin hc hb hE₁ hE₂)).trans
    ((lazy_budget_sharp hM).trans
      (QueryScanHistoryRealNumerics.dyadic_mono (by omega : 190 ≤ 204)))

include hN in
/-- Union over the 128 scan calls and at most q earlier entries, including
the digest. Total q includes honest calls; the observer runs afterwards. -/
theorem real_fresh_linear (hin : RAddrIn W Pr R h B outputs x w)
    (hc : RCausal W Pr h B outputs x w) (hb : RCommitBytes W Pr)
    (hE₁ : Pr.E₁ ≤ 2^64) (hE₂ : Pr.E₂ ≤ 2^64)
    (hM : N * n1 W Pr ≤ 2^25) (hN8 : N = 8) (q : ℕ)
    (hq : N * n1 W Pr + 1 ≤ q) :
    eventMass (realFresh W Pr N h B outputs x w) ≤ freshBudget q := by
  have hu := mass_exists_le_card
    (fun p : ScanStep N × Option (Fin (N * n1 W Pr)) =>
      priorHit W Pr N h B outputs x w p.1 p.2)
    (1 / (2 : ℚ)^190)
    (fun p => prior_hit_mass W Pr R N hN h B outputs x w hin hc hb hE₁ hE₂ hM p.1 p.2)
  have he : eventMass (realFresh W Pr N h B outputs x w) =
      mass (fun r => ∃ p : ScanStep N × Option (Fin (N * n1 W Pr)),
        priorHit W Pr N h B outputs x w p.1 p.2 r) := by
    unfold eventMass mass
    congr 1
    funext r
    have hh := fresh_iff_prior_hit W Pr N h B outputs x w r
    have hh' : realFresh W Pr N h B outputs x w r ↔
        ∃ p : ScanStep N × Option (Fin (N * n1 W Pr)), priorHit W Pr N h B outputs x w p.1 p.2 r := by
      simpa only [Prod.exists] using hh
    simp only [hh']
    split_ifs <;> rfl
  rw [he]
  apply hu.trans
  have hcard : Fintype.card (ScanStep N × Option (Fin (N * n1 W Pr))) =
      128 * (N * n1 W Pr + 1) := by
    simp [ScanStep, Fintype.card_prod, Fintype.card_fin, hN8]
    <;> omega
  rw [hcard]
  unfold freshBudget
  push_cast
  simp only [mul_one_div]
  gcongr
  exact_mod_cast hq

#print axioms scan_index_coverage
#print axioms fresh_iff_prior_hit
#print axioms prior_hit_mass
#print axioms real_fresh_linear
end R1Z.QueryScanFreshUnion
