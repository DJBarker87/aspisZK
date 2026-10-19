import ProgramQueryCost
import RRProgramAbortBound

namespace AspisR1.RRProgramQueryBound
open AspisR1.ProgramQueryCost AspisR1.RRProgramTraversal
open AspisR1.RRProgramAbortBound
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {I A K S X Y : Type}

theorem mapOption_cost_le (p : Program I A (Option X)) (f : X → Y)
    (B : Nat) (hp : AllCosts p (fun _ n => n ≤ B)) :
    AllCosts (mapOption p f) (fun _ n => n ≤ B) := by
  apply allCosts_bind
  apply allCosts_mono _ hp
  intro out n hn
  exact hn

theorem walkChildren_cost_le (run : S → Program I A (Option (List (List K))))
    (mass : S → Nat) (k : Nat)
    (hrun : ∀ s, AllCosts (run s) (fun _ n => n ≤ k * mass s))
    (cs : List (K × S)) :
    AllCosts (walkChildren run cs) (fun _ n => n ≤ k * childMass mass cs) := by
  induction cs with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    rcases head with ⟨a,s⟩
    change AllCosts (optionBind (run s) (fun ys =>
      mapOption (walkChildren run tail) (fun zs => ys.map (a :: ·) ++ zs))) _
    unfold optionBind
    apply allCosts_bind
    apply allCosts_mono _ (hrun s)
    intro out n hn
    cases out with
    | none =>
      change n+0 ≤ k * childMass mass ((a,s)::tail)
      simp only [childMass, List.map_cons, List.sum_cons, Nat.mul_add]
      omega
    | some ys =>
      apply allCosts_mono _ (mapOption_cost_le _ _ _ ih)
      intro out m hm
      have he : childMass mass ((a,s)::tail) = mass s + childMass mass tail := rfl
      rw [he, Nat.mul_add]
      exact Nat.add_le_add hn hm

/-- Local scalar-call costs and sibling mass conservation give a linear
whole-traversal ask bound on every branch, including aborting branches. -/
theorem collectProgram_cost_le (zeroTest : S → Bool)
    (children : S → Program I A (Option (List (K × S)))) (mass : S → Nat)
    (hlocal : ∀ s, AllCosts (children s) (fun out n => n ≤ mass s ∧
      ∀ cs, out = some cs → childMass mass cs ≤ mass s))
    (d : Nat) (s : S) :
    AllCosts (collectProgram zeroTest children d s) (fun _ n => n ≤ d * mass s) := by
  induction d generalizing s with
  | zero => exact Nat.zero_le _
  | succ d ih =>
    rw [collectProgram, optionBind]
    apply allCosts_bind
    apply allCosts_mono _ (hlocal s)
    intro out n hn
    cases out with
    | none =>
      change n+0 ≤ (d+1)*mass s
      rw [Nat.add_mul, Nat.one_mul]
      omega
    | some cs =>
      have hm := hn.2 cs rfl
      apply allCosts_mono _ (walkChildren_cost_le _ mass d ih cs)
      intro out m hm'
      have hmul := Nat.mul_le_mul_left d hm
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- The actual global tape cursor stays within the same bound after every
possible answer branch of the whole traversal. -/
theorem collectProgram_sequential_end_bound (zeroTest : S → Bool)
    (children : S → Program I A (Option (List (K × S)))) (mass : S → Nat)
    (hlocal : ∀ s, AllCosts (children s) (fun out n => n ≤ mass s ∧
      ∀ cs, out = some cs → childMass mass cs ≤ mass s))
    (d : Nat) (s : S) (cursor : Nat) :
    AspisR1.SequentialProgramInvariants.AllOutcomes
      (AspisR1.SequentialFreshProgram.sequential
        (collectProgram zeroTest children d s) cursor)
      (fun out => out.2 ≤ cursor + d * mass s) := by
  apply AspisR1.SequentialProgramInvariants.all_mono _
    (allCosts_sequential _ _ (collectProgram_cost_le zeroTest children mass hlocal d s) cursor)
  intro out ho
  obtain ⟨n,hn,hb⟩ := ho
  omega

theorem collectProgram_actual_trace_bound (zeroTest : S → Bool)
    (children : S → Program I A (Option (List (K × S)))) (mass : S → Nat)
    (hlocal : ∀ s, AllCosts (children s) (fun out n => n ≤ mass s ∧
      ∀ cs, out = some cs → childMass mass cs ≤ mass s))
    (d : Nat) (s : S) (cursor : Nat) (H : Nat → A) :
    (eval H (AspisR1.SequentialFreshProgram.sequential
      (collectProgram zeroTest children d s) cursor)).1.length ≤ d * mass s := by
  have hb := AspisR1.SequentialProgramInvariants.all_eval H _ _
    (collectProgram_sequential_end_bound zeroTest children mass hlocal d s cursor)
  have he := AspisR1.SequentialProgramInvariants.sequential_eval_cursor H
    (collectProgram zeroTest children d s) cursor
  omega

#print axioms collectProgram_actual_trace_bound
#print axioms collectProgram_sequential_end_bound
#print axioms mapOption_cost_le
#print axioms walkChildren_cost_le
#print axioms collectProgram_cost_le
end AspisR1.RRProgramQueryBound
