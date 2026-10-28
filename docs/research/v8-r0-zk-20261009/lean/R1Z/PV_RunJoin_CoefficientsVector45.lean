import R1Z.PV_RunJoin_CoefficientInstalled45
import R1Z.PV_RunJoin_Vector44
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientsVector45
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
-- Reducibility hints only; kernel checking and resource limits are unchanged.
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwFullSampler.install ProverRwCallerBinding.install ProverRwOuterContext.install ProverRwOuterTag.install ProverRwOuterTag.selected ProverRwOuterGuardLeaves.selected ProverRwSuccessHeapInstall.selected ProverRwSuccessErrorInstall.selected ProverRwSuccessNativeNegInstall.selected ProverRwSuccessNativeWideInstall.selected ProverRwBodyNativeWideInstall.selected ProverRwP6TransitionInstall.selected ProverRwP6FlatInstall.selected ProverRwP6BoundaryInstall.selected ProverRwSuccessBodyInterpretation.selected
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Column := Array W 1024#usize

def messages (p : Nat → Nat → W) : Slice Column :=
  Array.to_slice (ProverCommitArray49.array 29#usize (fun l => ProverCommitArray49.array 1024#usize (p l)))
def column (p : Nat → W) : Column := ProverCommitArray49.array 1024#usize (fun j => p (AspisR1.rowNat j))
def payload (p : Nat → Nat → W) (start : Nat) : Nat → List Column
  | 0 => []
  | n+1 => column (p start) :: payload p (start+1) n

theorem payload_length (p : Nat → Nat → W) (start n : Nat) : (payload p start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [payload,List.length_cons,ih]

theorem installed (ops : ExternalFuns) (p : Nat → W) :
    @transport.Variant.coefficients _ (ProverRwP6BodyCandidate.selected ops) _
      aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy .S2 (ProverCommitArray49.array 1024#usize p) =
        .ok (column p) := by
  exact PV_RunJoin_CoefficientInstalled45.complete ops _ p

theorem complete (ops : ExternalFuns) (p : Nat → Nat → W) (n : Nat)
    (out : alloc.vec.Vec Column) (lane : Usize) (bound : lane.val + n = 29)
    (room : out.length + n ≤ Usize.max) :
    ∃ next, @prover.opening_coefficients_loop _ (ProverRwP6BodyCandidate.selected ops) .S2
      (messages p) out lane = .ok next ∧ next.val = out.val ++ payload p lane.val n := by
  induction n generalizing out lane with
  | zero =>
    refine ⟨out,?_,by simp only [payload,List.append_nil]⟩
    unfold prover.opening_coefficients_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [prover.opening_coefficients_loop.body,
      show ¬lane < Slice.len (messages p) from (by change ¬lane.val < (messages p).length;rw [messages,Array.length_to_slice];change ¬lane.val < 29;omega),↓reduceIte,bind_tc_ok]
  | succ n ih =>
    have hi : lane.val < 29 := by omega
    have read : Slice.index_usize (messages p) lane = .ok (ProverCommitArray49.array 1024#usize (p lane.val)) :=
      PV_RunJoin_Vector44.read (A := Column) 29#usize (fun l => ProverCommitArray49.array 1024#usize (p l)) lane hi
    obtain ⟨mid,hm,hmv⟩ := PV_RunJoin_Vector44.push out (column (p lane.val)) (by omega)
    have ml : mid.length = out.length + 1 := by rw [show mid.length=mid.val.length from rfl,hmv,List.length_append,List.length_singleton]
    have inc := PV_RunJoin_MergeLoop35.increment lane (by omega)
    obtain ⟨next,hn,hnv⟩ := ih mid (Usize.wrapping_add lane 1#usize) (by rw [inc];omega) (by rw [ml];omega)
    refine ⟨next,?_,?_⟩
    · unfold prover.opening_coefficients_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      simp only [prover.opening_coefficients_loop.body,
        show lane < Slice.len (messages p) from (by change lane.val < (messages p).length;rw [messages,Array.length_to_slice];exact hi),↓reduceIte,read,bind_tc_ok,
        lift]
      rw [installed ops (p lane.val)]
      simp only [bind_tc_ok,hm]
      exact hn
    · rw [hnv,hmv,inc,payload,List.append_assoc,List.singleton_append]
#print axioms payload_length
#print axioms installed
#print axioms complete
end R1Z.PV_RunJoin_CoefficientsVector45
