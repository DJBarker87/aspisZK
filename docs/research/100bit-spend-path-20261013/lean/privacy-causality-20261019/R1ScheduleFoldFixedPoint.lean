import Init.Data.List.Pairwise
import Init.Data.List.Lemmas
import Lean.Elab.Tactic.Induction
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Simpa
import Lean.Elab.Tactic.RCases
import Lean.Elab.Tactic.Change

namespace R1ScheduleFold

variable {ι β γ : Type} [DecidableEq ι]

def put (s : ι → β) (i : ι) (v : β) : ι → β := fun k => if k = i then v else s k

def step (H : γ → β) (q : ι → (ι → β) → γ) (s : ι → β) (i : ι) : ι → β :=
  put s i (H (q i s))

def run (H : γ → β) (q : ι → (ι → β) → γ) (s : ι → β) (xs : List ι) : ι → β :=
  xs.foldl (step H q) s

def Causal (q : ι → (ι → β) → γ) : List ι → Prop
  | [] => True
  | i :: is =>
      (∀ k ∈ i :: is, ∀ s v, q i (put s k v) = q i s) ∧ Causal q is

theorem put_other {s : ι → β} {i j : ι} (h : i ≠ j) (v : β) : put s i v j = s j := by
  simp [put, h.symm]

theorem put_same {s : ι → β} {i : ι} (v : β) : put s i v i = v := by
  simp [put]

theorem fold_value_not_mem (H : γ → β) (q : ι → (ι → β) → γ)
    (s : ι → β) (xs : List ι) (i : ι) (hi : i ∉ xs) :
    run H q s xs i = s i := by
  induction xs generalizing s with
  | nil => rfl
  | cons j js ih =>
      simp only [run, List.foldl_cons]
      have hij : i ≠ j := by
        intro e
        subst i
        exact hi List.mem_cons_self
      have htail : i ∉ js := by
        intro h
        exact hi (List.mem_cons_of_mem _ h)
      change run H q (step H q s j) js i = s i
      rw [ih _ htail]
      simpa [step, put, hij.symm] using (put_other (s := s) (i := j) (j := i) hij.symm _ )

theorem fold_query_stable (H : γ → β) (q : ι → (ι → β) → γ)
    (xs : List ι) (s : ι → β) (i : ι)
    (hstable : ∀ k ∈ xs, ∀ s v, q i (put s k v) = q i s) :
    q i (run H q s xs) = q i s := by
  induction xs generalizing s with
  | nil => rfl
  | cons k ks ih =>
      simp only [run, List.foldl_cons]
      change q i (run H q (step H q s k) ks) = q i s
      rw [ih]
      · exact hstable k List.mem_cons_self s (H (q k s))
      · intro l hl st v
        exact hstable l (List.mem_cons_of_mem _ hl) st v

theorem schedule_fold_fixed_point
    (H : γ → β) (q : ι → (ι → β) → γ)
    (xs : List ι) (s : ι → β) (hcausal : Causal q xs) (hnodup : xs.Nodup)
    (i : ι) (hi : i ∈ xs) :
    run H q s xs i = H (q i (run H q s xs)) := by
  induction xs generalizing s with
  | nil => simp at hi
  | cons j js ih =>
      simp only [run, List.foldl_cons]
      rcases List.mem_cons.mp hi with hij | hi
      · subst i
        have htail : j ∉ js := by
          intro hj
          exact (List.nodup_cons.mp hnodup).1 hj
        change run H q (step H q s j) js j = H (q j (run H q (step H q s j) js))
        rw [fold_value_not_mem H q _ js j htail]
        simp only [step, put, if_pos]
        have hqHead : q j (put s j (H (q j s))) = q j s :=
          hcausal.1 j List.mem_cons_self s (H (q j s))
        have hqTail : q j (run H q (put s j (H (q j s))) js) = q j (put s j (H (q j s))) :=
          fold_query_stable H q js (put s j (H (q j s))) j
            (by intro k hk st v; exact hcausal.1 k (List.mem_cons_of_mem _ hk) st v)
        exact congrArg H (hqTail.trans hqHead).symm
      · apply ih
        · exact hcausal.2
        · exact (List.nodup_cons.mp hnodup).2
        · exact hi

/-- The transcript log built from final addresses and H agrees pointwise with
answers actually stored by the fold. This is the algebraic log-consistency
bridge consumed by realAttempt once its address query is prefix-causal. -/
theorem fold_log_consistent
    (H : γ → β) (q : ι → (ι → β) → γ)
    (xs : List ι) (s : ι → β) (hcausal : Causal q xs) (hnodup : xs.Nodup) :
    xs.map (fun i => (q i (run H q s xs), H (q i (run H q s xs)))) =
      xs.map (fun i => (q i (run H q s xs), run H q s xs i)) := by
  apply List.map_congr_left
  intro i hi
  have hfixed := schedule_fold_fixed_point H q xs s hcausal hnodup i hi
  exact Prod.ext rfl hfixed.symm

end R1ScheduleFold
#print axioms R1ScheduleFold.schedule_fold_fixed_point
