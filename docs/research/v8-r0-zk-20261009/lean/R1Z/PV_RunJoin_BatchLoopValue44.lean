import R1Z.PV_RunJoin_BatchRowAssociation44
import R1Z.PV_RunJoin_BatchThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BatchLoopValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_BatchRowValue44 (table array)
variable [ExternalTypes]

def payload (z : Nat → Raw) (start : Nat) : Nat → List W
  | 0 => []
  | n+1 => current (source (z start)) :: payload z (start+1) n

theorem payload_length (z : Nat → Raw) (start n : Nat) : (payload z start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [payload,List.length_cons,ih]

theorem complete (ops : ExternalFuns) (c : Nat → Nat → Raw) (p z : Nat → Raw)
    (hc : ∀ l, l < 29 → ∀ j, j < 1024 → canonical (c l j))
    (hp : ∀ l, l < 29 → canonical (p l))
    (hz : ∀ j, j < 1024 → canonical (z j))
    (hd : ∀ j, j < 1024 → value (z j) = sum (fun l => c l j) p 29 0)
    (n : Nat) (out : alloc.vec.Vec W) (row : Usize) (bound : row.val + n = 1024)
    (room : out.length + n ≤ Usize.max) :
    ∃ next, @PV_RunJoin_BatchThread44.phase _ (ProverRwP6BodyCandidate.selected ops)
      (table c) (array 29#usize p) n out row = .ok next ∧
      next.val = out.val ++ payload z row.val n := by
  induction n generalizing out row with
  | zero => exact ⟨out,rfl,by simp only [payload,List.append_nil]⟩
  | succ n ih =>
    have hr : row.val < 1024 := by omega
    obtain ⟨y,hy,_,hcy,hdy⟩ := PV_RunJoin_BatchRowAssociation44.complete ops c p hc hp row hr
    have same : y = z row.val := PV_RunJoin_WideUnique44.unique y (z row.val) hcy (hz _ hr)
      (hdy.trans (hd _ hr).symm)
    rw [same] at hy
    obtain ⟨mid,hm,hmv⟩ := PV_RunJoin_Vector44.push out (current (source (z row.val))) (by omega)
    have ml : mid.length = out.length + 1 := by rw [show mid.length=mid.val.length from rfl,hmv,List.length_append,List.length_singleton];rfl
    have inc := PV_RunJoin_MergeLoop35.increment row (by omega)
    obtain ⟨next,hn,hnv⟩ := ih mid (Usize.wrapping_add row 1#usize) (by rw [inc];omega) (by rw [ml];omega)
    refine ⟨next,?_,?_⟩
    · simp only [PV_RunJoin_BatchThread44.phase,PV_RunJoin_BatchThread44.step,hy,hm,bind_tc_ok,hn]
    · rw [hnv,hmv,inc,payload,List.append_assoc,List.singleton_append]
#print axioms payload_length
#print axioms complete
end R1Z.PV_RunJoin_BatchLoopValue44
