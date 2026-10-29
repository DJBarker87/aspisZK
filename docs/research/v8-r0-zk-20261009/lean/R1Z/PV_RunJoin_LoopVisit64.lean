import R1Z.ProverRw19LoopBind
import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LoopVisit64
open Aeneas Aeneas.Std Result

/-- Invert an already successful source loop at a selected visited index.
The symbolic distance decreases; the concrete loop is never kernel-replayed. -/
theorem visited {A B : Type} (step : A → Result (ControlFlow A B))
    (index : A → Nat) (P : Nat → Prop) (count target : Nat)
    (progress : ∀ a cf, index a<count → step a=ok cf →
      ∃ next, cf=.cont next ∧ index next=index a+1 ∧ P (index a))
    (bound : target<count) (n : Nat) (a : A) (rank : index a+n=target)
    (b : B) (success : loop step a=ok b) : P target := by
  induction n generalizing a with
  | zero =>
    rw [ProverRw19LoopBind.loop_bind] at success
    obtain ⟨cf,hcf,htail⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
    obtain ⟨next,hnext,hn,hc⟩ := progress a cf (by omega) hcf
    have same : index a=target := by omega
    exact same ▸ hc
  | succ n ih =>
    rw [ProverRw19LoopBind.loop_bind] at success
    obtain ⟨cf,hcf,htail⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
    obtain ⟨next,hnext,hn,hc⟩ := progress a cf (by omega) hcf
    rw [hnext] at htail
    exact ih next (by omega) htail

#print axioms visited
end R1Z.PV_RunJoin_LoopVisit64
