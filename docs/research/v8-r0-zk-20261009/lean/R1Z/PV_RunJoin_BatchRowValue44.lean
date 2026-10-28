import R1Z.PV_RunJoin_BatchRowThread44
import R1Z.PV_RunJoin_Vector44
import R1Z.ProverCommitGammaOutput53
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BatchRowValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact

def array (size : Usize) (xs : Nat → Raw) :=
  ProverCommitArray49.array size (fun i => current (source (xs i)))
def table (c : Nat → Nat → Raw) :=
  Array.to_slice (ProverCommitArray49.array 29#usize (fun l => array 1024#usize (c l)))

attribute [local irreducible] source value canonical

theorem step (ops : ExternalFuns) (c : Nat → Nat → Raw) (p : Nat → Raw)
    (row lane : Usize) (hr : row.val < 1024) (hl : lane.val < 29)
    (s : Raw) (hs : canonical s) (hp : canonical (p lane.val))
    (hc : canonical (c lane.val row.val)) :
    ∃ z : Raw, @PV_RunJoin_BatchRowThread44.step _ (ProverRwP6BodyCandidate.selected ops)
      (table c) (array 29#usize p) row lane (current (source s)) = .ok (current (source z)) ∧
      canonical z ∧ value z = value s + value (p lane.val) * value (c lane.val row.val) := by
  obtain ⟨product,hprod,hcprod,hdprod⟩ := mul_exact (p lane.val) (c lane.val row.val) hp hc
  obtain ⟨z,hz,hcz,hdz⟩ := add_exact s product hs hcprod
  refine ⟨z,?_,hcz,by rw [hdz,hdprod]⟩
  unfold PV_RunJoin_BatchRowThread44.step table array
  rw [ProverCommitArray49.index 29#usize (fun i => current (source (p i))) lane hl]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_Vector44.read (A := Array W 1024#usize) 29#usize (fun (l : Nat) => ProverCommitArray49.array 1024#usize (fun i => current (source (c l i)))) lane hl]
  simp only [bind_tc_ok]
  rw [ProverCommitArray49.index 1024#usize (fun i => current (source (c lane.val i))) row hr]
  simp only [bind_tc_ok,PV_RunJoin_WideArithmetic44.mul ops _ _ _ hprod,
    PV_RunJoin_WideArithmetic44.add ops _ _ _ hz]

theorem phase (ops : ExternalFuns) (c : Nat → Nat → Raw) (p : Nat → Raw)
    (row : Usize) (hr : row.val < 1024)
    (hc : ∀ l, l < 29 → canonical (c l row.val)) (hp : ∀ l, l < 29 → canonical (p l))
    (n : Nat) (lane : Usize) (bound : lane.val + n ≤ 29) (s : Raw) (hs : canonical s) :
    ∃ z : Raw, @PV_RunJoin_BatchRowThread44.phase _ (ProverRwP6BodyCandidate.selected ops)
      (table c) (array 29#usize p) row n lane (current (source s)) = .ok (current (source z)) ∧
      canonical z ∧ value z = value s + sum (fun l => c l row.val) p n lane.val := by
  induction n generalizing lane s with
  | zero => exact ⟨s,rfl,hs,by rw [sum,add_zero]⟩
  | succ n ih =>
    have hl : lane.val < 29 := by omega
    obtain ⟨next,hn,hcn,hdn⟩ := step ops c p row lane hr hl s hs (hp _ hl) (hc _ hl)
    have inc := PV_RunJoin_MergeLoop35.increment lane (by omega)
    obtain ⟨z,hz,hcz,hdz⟩ := ih (Usize.wrapping_add lane 1#usize) (by rw [inc];omega) next hcn
    refine ⟨z,?_,hcz,?_⟩
    · simp only [PV_RunJoin_BatchRowThread44.phase,hn,bind_tc_ok,hz]
    · rw [hdz,hdn,inc,sum]
      ring
#print axioms step
#print axioms phase
end R1Z.PV_RunJoin_BatchRowValue44
