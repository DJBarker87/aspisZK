import R1Z.GamesR1
import R1Z.TranscriptR1
import R1ScheduleFoldFixedPoint

set_option autoImplicit false
noncomputable section
namespace R1Z.TranscriptR1
open R1ScheduleFold R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS
  R0Z.FsAbortBounds R1Z.Batched R1Z.ModelsVR1 R1Z.LensR1

/-- The address query with a final record's message bytes held fixed. This is
not the realAttempt view-dependent query; it is the source-layout layer for
which `addr_setC_of_not_dep` applies directly. -/
def fixedRestQuery (rest : Rest) (c1 : Ans) (kstar : Fin 8)
    (j : TRead) (tr : TRead → Ans) : List UInt8 :=
  addr j ⟨tr, c1, kstar, rest⟩

/-- Schedule dependency certificate: at each query, none of the answer cells
at or after that query is its designated address coordinate. -/
def NoFutureDep : List TRead → Prop
  | [] => True
  | j :: js =>
      (∀ k ∈ j :: js, ¬ Dep (fc j) (.ans k)) ∧ NoFutureDep js

theorem fixedRestQuery_causal (rest : Rest) (c1 : Ans) (kstar : Fin 8)
    (xs : List TRead) (hdep : NoFutureDep xs) :
    R1ScheduleFold.Causal (fixedRestQuery rest c1 kstar) xs := by
  induction xs with
  | nil => trivial
  | cons j js ih =>
      rcases hdep with ⟨hhead, htail⟩
      refine ⟨?_, ih htail⟩
      intro k hk tr v
      have hrec : (⟨put tr k v, c1, kstar, rest⟩ : Rec) =
          setC (.ans k) (⟨tr, c1, kstar, rest⟩ : Rec) v := by
        simp only [setC, Rec.mk.injEq]
        constructor
        · funext l
          simp [put, Function.update]
        · simp
      change addr j (⟨put tr k v, c1, kstar, rest⟩ : Rec) =
        addr j (⟨tr, c1, kstar, rest⟩ : Rec)
      rw [hrec]
      exact addr_setC_of_not_dep j (.ans k) ⟨tr, c1, kstar, rest⟩ v (hhead k hk)



/-- Executable dependency test used to decide the concrete finite schedule. -/
def depB : Coord → Coord → Bool
  | .root, .root => true
  | .sel, .sel => true
  | .ans j, .ans k => decide (j = k)
  | .sel, .ans j => decide (∃ k : Fin 8, j = .qa k)
  | .ans j, .sel => decide (∃ k : Fin 8, j = .qa k)
  | _, _ => false

theorem depB_true_iff (c c' : Coord) : depB c c' = true ↔ Dep c c' := by
  cases c <;> cases c' <;> simp [depB, Dep]

theorem depB_false_iff (c c' : Coord) : depB c c' = false ↔ ¬ Dep c c' := by
  constructor
  · intro hb hd
    have ht : depB c c' = true := (depB_true_iff c c').2 hd
    rw [hb] at ht
    cases ht
  · intro hn
    cases hb : depB c c' with
    | false => rfl
    | true =>
        exfalso
        exact hn ((depB_true_iff c c').1 hb)

def noFutureB : List TRead → Bool
  | [] => true
  | j :: js => (j :: js).all (fun k => !(depB (fc j) (.ans k))) && noFutureB js

theorem noFutureB_true_iff (xs : List TRead) :
    noFutureB xs = true ↔ NoFutureDep xs := by
  induction xs with
  | nil => simp [noFutureB, NoFutureDep]
  | cons j js ih =>
      simp [noFutureB, NoFutureDep, ih, depB_false_iff, List.all_eq_true]

theorem schedule_noFutureDep : NoFutureDep schedule :=
  (noFutureB_true_iff schedule).mp (by decide)

theorem schedule_nodup : schedule.Nodup := by
  decide

/-- For fixed serialized row messages, the hash-fold answer at each scheduled
read is the hash of its final-record address. Instantiating `NoFutureDep` for
the canonical 115-read schedule is a finite schedule/dependency obligation. -/
theorem fixedRest_fold_fixed_point
    (H : List UInt8 → Ans) (rest : Rest) (c1 : Ans) (kstar : Fin 8)
    (xs : List TRead) (s : TRead → Ans)
    (hdep : NoFutureDep xs) (hnodup : xs.Nodup) (j : TRead) (hj : j ∈ xs) :
    R1ScheduleFold.run H (fixedRestQuery rest c1 kstar) s xs j =
      H (fixedRestQuery rest c1 kstar j
        (R1ScheduleFold.run H (fixedRestQuery rest c1 kstar) s xs)) := by
  exact R1ScheduleFold.schedule_fold_fixed_point H _ xs s
    (fixedRestQuery_causal rest c1 kstar xs hdep) hnodup j hj

theorem fixedRest_canonical_schedule_fold_fixed_point
    (H : List UInt8 → Ans) (rest : Rest) (c1 : Ans) (kstar : Fin 8)
    (s : TRead → Ans) (j : TRead) :
    R1ScheduleFold.run H (fixedRestQuery rest c1 kstar) s schedule j =
      H (fixedRestQuery rest c1 kstar j
        (R1ScheduleFold.run H (fixedRestQuery rest c1 kstar) s schedule)) := by
  exact fixedRest_fold_fixed_point H rest c1 kstar schedule s
    schedule_noFutureDep schedule_nodup j (mem_schedule j)

end R1Z.TranscriptR1
