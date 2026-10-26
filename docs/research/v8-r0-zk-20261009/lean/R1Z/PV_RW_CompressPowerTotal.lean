import R1Z.PV_RW_CompressPowerFold
import R1Z.PV_RW_CompressNativePower
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressPowerTotal
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem mul (power lambda : Q) : ∃ next, qMul power lambda=ok next := by
  obtain ⟨next,hn⟩ := ProverRwP6QuarticTotal.mul (toQ power) (toQ lambda)
  exact ⟨fromQ next,by simp only [qMul,hn,mapResult]⟩

theorem run (lambda : Q) (n : Nat) (power : Q) :
    ∃ final, PV_RW_CompressPowerFold.powerRun lambda n power=ok final := by
  induction n generalizing power with
  | zero => exact ⟨power,rfl⟩
  | succ n ih =>
    obtain ⟨next,hn⟩ := mul power lambda
    obtain ⟨final,hf⟩ := ih next
    exact ⟨final,by simpa only [PV_RW_CompressPowerFold.powerRun,hn,bind_tc_ok] using hf⟩
#print axioms mul
#print axioms run
end R1Z.PV_RW_CompressPowerTotal
