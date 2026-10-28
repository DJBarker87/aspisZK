import NCM_RowProgress

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Rows
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts NCE_CarrierEffects
open MultiproofConeNodeDomain MultiproofConePhysicalTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Run := Program Bytes State (Result reference.Level × Carrier)
def modelExit (s : Carrier) (w : Usize) : Carrier := {s with scratch:={s.scratch with n:=w}}
def terminal (exit : NCE_VerifierCuts.Exit) (s : Carrier) (i w : Usize) : Run :=
  if i≥s.scratch.n then
    let after := exit s w
    .done (ok (.Done after.scratch),after)
  else .done (.div,s)

/-- Native carrier recursion: every continuation consumes THAT row's caller,
including the actual accumulated log. Fuel is only the induction index. -/
def rows (node : Node) (exit : NCE_VerifierCuts.Exit) :
    Nat → Carrier → Slice U8 → Usize → Usize → Run
  | 0,s,_,i,w => terminal exit s i w
  | fuel+1,s,physical,i,w =>
    if i≥s.scratch.n then terminal exit s i w else
    bind (node s physical i w) fun returned =>
      match returned.1 with
      | .fail error => .done (.fail error,returned.2)
      | .div => .done (.div,returned.2)
      | .ok (.Stop stopped) => .done (ok (.Stop stopped),returned.2)
      | .ok (.Next _ ni nw) => rows node exit fuel returned.2 physical ni nw

/-- All-outcome row-loop association from ONE native row and exhausted-row
control. Progress, recursive domain and external caller frame are derived. -/
theorem association {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input = ok (rawOracle H input))
    (native : Node) (cut : NCE_Native_Row H native)
    (entry : NCE_VerifierCuts.Entry) (exit : NCE_VerifierCuts.Exit)
    (finish : NCE_VerifierCuts.Finish)
    (control : NCE_VerifierCuts.NCE_Native_Verifier entry exit finish)
    (fuel : Nat) (s : Carrier) (physical : Slice U8) (i w : Usize)
    (size : physical.val.length ≤ 5504) (domain : RowDomain physical s.scratch i w) :
    eval H (rows native exit fuel s physical i w) =
      eval H (rows NCM_RowProgress.model modelExit fuel s physical i w) := by
  have exitEq : ∀ (c : Carrier) (w : Usize), w.val ≤ 16 → exit c w = modelExit c w :=
    fun c w bound => control.2.1 c w bound
  induction fuel generalizing s i w with
  | zero =>
    simp only [rows,terminal]
    split
    · rw [exitEq s w (by obtain ⟨_,ns,ib,wb,_⟩ := domain; omega)]
    · rfl
  | succ fuel ih =>
    simp only [rows]
    by_cases halt : i≥s.scratch.n
    · simp only [halt,if_true,terminal]
      rw [exitEq s w (by obtain ⟨_,ns,ib,wb,_⟩ := domain; omega)]
    · simp only [halt,if_false,eval_bind]
      have active : i.val < s.scratch.n.val := by scalar_tac
      obtain ⟨out,log,observed,post⟩ := NCM_RowProgress.progress D hash H law native cut s physical i w size domain active
      have modeled := (cut s physical i w size domain active).symm.trans observed
      change eval H (NCM_RowProgress.model s physical i w) = _ at modeled
      rw [observed,modeled]
      cases out with
      | Stop stopped => rfl
      | Next after ni nw =>
        simp only [rowScratch]
        have next := ih {s with scratch:=after,log:=s.log++log} ni nw post.2.1
        simp only [next]

#print axioms association
end AspisR1.NCM_Rows
end
