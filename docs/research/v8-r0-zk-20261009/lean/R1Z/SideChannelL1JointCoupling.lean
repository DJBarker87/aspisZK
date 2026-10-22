import R1Z.SideChannelRetryLaw
import R1Z.ProverCommitEntropyCharge40
import R0Z.AbsorptionLaw

/-! Generic L1 joint-bound tools and a marginal-to-joint obstruction.
There is deliberately NO deployed L1 privacy theorem here: the concrete
joint source agreement and bad-event bounds remain to be instantiated.
A published-view equality alone cannot justify that instantiation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SideChannelL1JointCoupling
open R0Z R0Z.FsAbortBounds
attribute [local instance] Classical.propDecidable
variable {Sample View : Type} [Fintype Sample]

/-- Coupling inequality for arbitrary output types, including full records
paired with the published proof and ordered adversary oracle observations. -/
theorem dist_le_bad (left right : Sample → View) (bad : Sample → Prop)
    (agree : ∀ s, ¬bad s → left s = right s) : dist left right ≤ mass bad := by
  let outputs := support left ∪ support right
  have memLeft (s : Sample) : left s ∈ outputs :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ s,rfl⟩)
  have memRight (s : Sample) : right s ∈ outputs :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ s,rfl⟩)
  let delta := fun (s : Sample) (v : View) =>
    |(if left s = v then (1 : ℚ) else 0) - (if right s = v then 1 else 0)|
  have pointwise (s : Sample) : (∑ v ∈ outputs, delta s v) ≤ if bad s then 2 else 0 := by
    by_cases hb : bad s
    · rw [if_pos hb]
      have indBound (v : View) : delta s v ≤
          (if left s = v then (1 : ℚ) else 0) + (if right s = v then 1 else 0) := by
        by_cases hl : left s = v <;> by_cases hr : right s = v <;> simp [delta,hl,hr]
      calc (∑ v ∈ outputs, delta s v) ≤
          ∑ v ∈ outputs, ((if left s = v then (1 : ℚ) else 0) + (if right s = v then 1 else 0)) :=
            Finset.sum_le_sum (fun v _ => indBound v)
        _ = 2 := by
          rw [Finset.sum_add_distrib]
          simp only [eq_comm,Finset.sum_ite_eq',if_pos (memLeft s),if_pos (memRight s)]
          norm_num
    · rw [if_neg hb]
      have same := agree s hb
      simp only [delta,same,sub_self,abs_zero,Finset.sum_const_zero,le_refl]
  have absBound (v : View) : |law left v-law right v| ≤ mean (fun s => delta s v) := by
    change |mean (fun s => if left s=v then (1 : ℚ) else 0) -
      mean (fun s => if right s=v then (1 : ℚ) else 0)| ≤ _
    rw [R0Z.FsGood.mean_sub]
    exact R0Z.FsGood.abs_mean_le _
  have interchange : (∑ v ∈ outputs, mean (fun s => delta s v)) =
      mean (fun s => ∑ v ∈ outputs, delta s v) := by
    unfold mean
    rw [Finset.sum_comm,Finset.sum_div]
  have indicator : (fun s => if bad s then (2 : ℚ) else 0) =
      fun s => (if bad s then (1 : ℚ) else 0)*2 := by
    funext s
    split_ifs <;> norm_num
  calc dist left right ≤ (∑ v ∈ outputs, mean (fun s => delta s v))/2 := by
        unfold R0Z.dist
        exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun v _ => absBound v)) (by norm_num)
    _ = mean (fun s => ∑ v ∈ outputs, delta s v)/2 := by rw [interchange]
    _ ≤ mean (fun s => if bad s then (2 : ℚ) else 0)/2 :=
      div_le_div_of_nonneg_right (mean_mono' _ _ pointwise) (by norm_num)
    _ = mass bad := by rw [indicator,mean_mul_const]; unfold mass; ring

/-- Each named event occurs once in the union. Whether it has an existing
charge or a new charge must be decided by the CONCRETE source instantiation. -/
theorem joint_union_bound {Kind : Type} [Fintype Kind]
    (left right : Sample → View) (bad : Kind → Sample → Prop) (budget : Kind → ℚ)
    (agree : ∀ s, (∀ kind, ¬bad kind s) → left s = right s)
    (bounded : ∀ kind, mass (bad kind) ≤ budget kind) :
    dist left right ≤ ∑ kind, budget kind := by
  have close := dist_le_bad left right (fun s => ∃ kind, bad kind s)
    (fun s h => agree s (fun kind hk => h ⟨kind,hk⟩))
  exact close.trans ((mass_exists_le bad).trans (Finset.sum_le_sum (fun kind _ => bounded kind)))

/-- Reused part-40 arithmetic only. This does not supply the missing joint
agreement, equal-circle/query laws or semantic guard refinements. -/
theorem retained_envelope_lt_target {scan q attempts : Nat}
    (hs : scan ≤ 2^65) (hq : q ≤ 2^64) (ha : attempts ≤ 128) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge +
      4 * ProverCommitPrivateMemo40.budget q attempts +
      16 * ProverCommitEntropyCharge40.zeroBudget < 1 / (2 : ℚ)^100 :=
  ProverCommitEntropyCharge40.total_lt_target hs hq ha

/-- Worst-budget TWO-witness arithmetic candidate, via a common simulator.
The factor two is explicit; no deployed joint-TV instance is asserted. The
existing event charges appear once per world, not again as new L1 charges. -/
theorem two_witness_candidate_numeric :
    2 * (1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      1 / (2 : ℚ)^118 + 2 / (2 : ℚ)^192 +
      48 / (2147483647 : ℚ)^5 + 1 / (2 : ℚ)^183 + 48 / (2 : ℚ)^256) <
        1 / (2 : ℚ)^100 := by
  rw [show (2 : ℚ)^454 = 2^227 * 2^227 by rw [←pow_add]]
  norm_num

/-! Tiny COUNTERMODEL TO A PROOF INFERENCE, not a valid-spend attack.
Both published bits are uniform; both count marginals agree. Their joint
law reveals the witness bit perfectly. Thus separate marginal theorems do
not close L1. The toy is not asserted to be implemented by the prover. -/
def flip : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

def toyPublished (w coin : Bool) := Bool.xor w coin
def toyCount (coin : Bool) : Nat := if coin then 1 else 2
def toyJoint (w coin : Bool) := (toyPublished w coin,toyCount coin)
def distinguishes (x : Bool × Nat) : Prop := (x.1 = true ↔ x.2 = 1)

theorem toy_public_laws : EqualLaws (toyPublished false) (toyPublished true) := by
  have same : (fun coin => toyPublished false (flip coin)) = toyPublished true := by
    funext coin
    cases coin <;> rfl
  rw [←same]
  intro value
  exact (AbsorptionLaw.law_equiv flip (toyPublished false) value).symm

theorem toy_count_laws : EqualLaws (fun coin => (toyJoint false coin).2)
    (fun coin => (toyJoint true coin).2) := by intro value; rfl

theorem toy_left_test : mass (fun coin => distinguishes (toyJoint false coin)) = 1 := by
  have h : (fun coin => distinguishes (toyJoint false coin)) = fun _ => True := by
    funext coin
    cases coin <;> simp [distinguishes,toyJoint,toyPublished,toyCount]
  rw [h,mass_true]

theorem toy_right_test : mass (fun coin => distinguishes (toyJoint true coin)) = 0 := by
  have h : (fun coin => distinguishes (toyJoint true coin)) = fun _ => False := by
    funext coin
    cases coin <;> simp [distinguishes,toyJoint,toyPublished,toyCount]
  rw [h,mass_false]

#print axioms dist_le_bad
#print axioms joint_union_bound
#print axioms retained_envelope_lt_target
#print axioms two_witness_candidate_numeric
#print axioms toy_public_laws
#print axioms toy_count_laws
#print axioms toy_left_test
#print axioms toy_right_test
end R1Z.SideChannelL1JointCoupling
