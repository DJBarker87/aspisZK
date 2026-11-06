import NKY_LevelSchedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_LevelsLoop
open Aeneas Aeneas.Std Result ControlFlow
open NJX_AppendDomains (Frontier High)
open NJX_DigestCohort (O)
open NJX_AppendFold (State)
open NKY_LevelCarrier (Pair pair)

/-- Exact emitted Result loop versus LevelsFrame, including failure/divergence
at every operation. Finite induction uses control only; field reductions are
never unfolded. -/
theorem association (index : U64) (f : Frontier) (o : O) (s : High)
 (fuel : Nat) (level : Usize) (before : State) (span : level.val+fuel=20) :
 NKY_LevelsLiteral.loop NKY_LevelsLiteral.child index f o s (pair before).1 (pair before).2 level=
 (do let after ← NKI_LevelsFrame.run index f o s
      (NKY_LevelSchedule.levels level.val fuel (by omega)) before
     ok (pair after)) := by
 induction fuel generalizing level before with
 | zero =>
  rw [NKY_LevelsLiteral.loop.eq_def,
   NKY_LevelsLiteral.done _ _ _ _ _ _ _ _ (by change ¬level.val<20;omega)]
  simp only [bind_tc_ok,NKY_LevelSchedule.levels,NKI_LevelsFrame.run]
 | succ n ih =>
  have hl : level.val<20 := by omega
  let next : Usize := UScalar.ofNatCore (level.val+1) (by scalar_tac)
  have inc : level+1#usize=ok next := by
   apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
  rw [NKY_LevelsLiteral.loop.eq_def,NKY_LevelsBody.source index f o s before level hl]
  rw [NKY_LevelSchedule.levels,NKI_LevelsFrame.run]
  simp only [bind_assoc_eq,inc,bind_tc_ok]
  apply congrArg
  funext child
  apply congrArg
  funext middle
  exact ih next middle (by have hn : next.val=level.val+1 := rfl;omega)

/-- The literal ZERO initialization and full returned pair, SAME arguments. -/
theorem entry (index : U64) (f : Frontier) (o : O) (s : High) :
 NKY_LevelsLiteral.append_levels_packed_selector_tensor NKY_LevelsLiteral.child index f o s=
 (do let after ← NKI_LevelsFrame.run index f o s (List.finRange 20) NKI_LevelsRoot.zero
     ok (pair after)) := by
 have h:=association index f o s 20 0#usize NKI_LevelsRoot.zero (by rfl)
 have sched : NKY_LevelSchedule.levels (0#usize).val 20 (by decide)=List.finRange 20 :=
  NKY_LevelSchedule.complete
 rw [sched] at h
 exact h
#print axioms association
#print axioms entry
end AspisR1.NKY_LevelsLoop
end
