import PV_L2C_PaddingProducer
set_option autoImplicit false
namespace PV_L2C_PaddingConsumer
open PV_L2C_PaddingProducer
variable {A : Type} [AddCommGroup A] [DecidableEq A]
/-- Per-row rejection branch of check_h1_padding_active. -/
def activeReject (active : Bool) (value : A) : Bool := active && decide (value≠0)
/-- Inactive-sum rejection branch of apply_h1_padding_mask_for_active. -/
def sumReject {n : Nat} (active : Fin n → Bool) (v : Fin n → A) : Bool :=
  decide (inactiveSum active v≠0)

theorem active_branch {n : Nat} (active : Fin n → Bool) (d : Fin n)
    (random : Fin n → A) (hd : active d=false) (i : Fin n) :
    activeReject (active i) (balanced active d (sampled active d random) i)=false := by
  cases hi : active i with
  | false => simp [activeReject,hi]
  | true => simp [activeReject,hi,balanced_active active d random hd i hi]
#print axioms active_branch

theorem sum_branch {n : Nat} (active : Fin n → Bool) (d : Fin n)
    (random : Fin n → A) (hd : active d=false) :
    sumReject active (balanced active d (sampled active d random))=false := by
  simp [sumReject,balanced_sum active d _ hd]
#print axioms sum_branch

/-- Every finite prefix of the actual active-row check has no early return. -/
def scan (rows : List Bool) : Bool := rows.any id

theorem scan_false (rows : List Bool) (h : ∀ b ∈ rows, b=false) : scan rows=false := by
  induction rows with
  | nil => rfl
  | cons b bs ih =>
    simp only [scan,List.any_cons]
    rw [h b (by simp)]
    simpa [scan] using ih (fun b hb => h b (by simp [hb]))
#print axioms scan_false

theorem all_active_branches {n : Nat} (active : Fin n → Bool) (d : Fin n)
    (random : Fin n → A) (hd : active d=false) (rows : List (Fin n)) :
    scan (rows.map (fun i => activeReject (active i)
      (balanced active d (sampled active d random) i)))=false := by
  apply scan_false
  intro b hb
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
  exact active_branch active d random hd i
#print axioms all_active_branches
end PV_L2C_PaddingConsumer
