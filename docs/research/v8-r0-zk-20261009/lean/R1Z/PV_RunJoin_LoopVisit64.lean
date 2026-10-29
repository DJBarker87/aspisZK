import R1Z.ProverRw19LoopBind
import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LoopVisit64
open Aeneas Aeneas.Std Result

/-- Invert an already successful source loop at a selected visited index.
The symbolic distance decreases; the concrete loop is never kernel-replayed. -/
theorem probe {A B C : Type} (step : A → Result (ControlFlow A B))
    (index : A → Nat) (read : Nat → Result C) (count target : Nat)
    (progress : ∀ a cf, index a<count → step a=ok cf →
      ∃ next, cf=.cont next ∧ index next=index a+1 ∧ ∃ c,read (index a)=ok c)
    (bound : target<count) (n : Nat) (a : A) (rank : index a+n=target)
    (b : B) (success : loop step a=ok b) : ∃ c,read target=ok c := by
  induction n generalizing a with
  | zero =>
    rw [ProverRw19LoopBind.loop_bind] at success
    obtain ⟨cf,hcf,htail⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
    obtain ⟨next,hnext,hn,c,hc⟩ := progress a cf (by omega) hcf
    exact ⟨c,by simpa only [Nat.add_zero] using rank ▸ hc⟩
  | succ n ih =>
    rw [ProverRw19LoopBind.loop_bind] at success
    obtain ⟨cf,hcf,htail⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
    obtain ⟨next,hnext,hn,c,hc⟩ := progress a cf (by omega) hcf
    rw [hnext] at htail
    exact ih next (by omega) htail

#print axioms probe
end R1Z.PV_RunJoin_LoopVisit64
