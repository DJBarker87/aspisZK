import R1Z.PV_RunJoin_SourceInitialRounds
import R1Z.PV_RunJoin_SourceFinalRounds
import R1Z.PV_RunJoin_SourceInternalRounds

/-! Erase the actual node compressor's no-op callback after the source round
recurrences have been proved. No callback error/state is assumed away: the
particular shipped callback computes `ok ((),())`. This is a root-helper
predecessor, not a Records or compiler-return association. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ParentNoopRounds
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_SourceRoundFold

abbrev callback : core.ops.function.FnMut Unit poseidon2.Poseidon2RoundTransition Unit :=
  poseidon2.merkle_node_compress_v3.closure.Insts.CoreOpsFunctionFnMutTuplePoseidon2RoundTransitionTuple

theorem callback_eq (t : poseidon2.Poseidon2RoundTransition) :
    callback.call_mut () t = ok ((),()) := rfl

def full (xs : List (Usize × State)) (s : State) : Result State :=
  match xs with
  | [] => ok s
  | (_,c)::tail => do
    let out ← R0PoseidonCopy.full_round s c
    full tail out

def internal (xs : List (Usize × U32)) (s : State) : Result State :=
  match xs with
  | [] => ok s
  | (_,c)::tail => do
    let out ← R0PoseidonCopy.internal_round s c R0PoseidonCopy.INTERNAL_SHIFTS
    internal tail out

theorem full_noop (kind : Usize → poseidon2.Poseidon2RoundKind)
    (xs : List (Usize × State)) (s input : State) (round : U8) :
    (do
      let p ← fullSteps callback kind xs s () round input
      ok p.1) = full xs s := by
  induction xs generalizing s input round with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨index,c⟩
    obtain ⟨out,ho,_⟩ := full_total s c
    simp only [fullSteps,full,ho,bind_tc_ok,callback_eq]
    exact ih out out (U8.wrapping_add round 1#u8)

theorem internal_noop (xs : List (Usize × U32))
    (s input : State) (round : U8) :
    (do
      let p ← PV_RunJoin_SourceInternalRounds.steps callback xs s () round input
      ok p.1) = internal xs s := by
  induction xs generalizing s input round with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨index,c⟩
    obtain ⟨out,ho,_⟩ := PV_RunJoin_SourceInternalRounds.total s c
    simp only [PV_RunJoin_SourceInternalRounds.steps,internal,ho,bind_tc_ok,callback_eq]
    exact ih out out (U8.wrapping_add round 1#u8)

theorem initial_source (iter : PV_RunJoin_SourceInitialRounds.Iter)
    (xs : List (Usize × State))
    (ht : BuilderStdModels.FiniteTrace PV_RunJoin_SourceInitialRounds.iterator iter xs)
    (s input : State) (round : U8) (hs : Canonical s)
    (hc : ∀ p ∈ xs, Canonical p.2) :
    (do
      let p ← poseidon2.permute_optimized_with_trace_loop0
        (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
        callback iter s () round input
      ok p.1) = full xs s := by
  rw [PV_RunJoin_SourceInitialRounds.source callback iter xs ht s input () round hs hc]
  exact full_noop _ xs s input round

theorem final_source (iter : PV_RunJoin_SourceFinalRounds.Iter)
    (xs : List (Usize × State))
    (ht : BuilderStdModels.FiniteTrace PV_RunJoin_SourceFinalRounds.iterator iter xs)
    (s input : State) (round : U8) (hs : Canonical s)
    (hc : ∀ p ∈ xs, Canonical p.2) :
    (do
      let p ← poseidon2.permute_optimized_with_trace_loop2
        (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
        callback iter s () round input
      ok p.1) = full xs s := by
  rw [PV_RunJoin_SourceFinalRounds.source callback iter xs ht s input () round hs hc]
  simpa only [bind_assoc_eq,bind_tc_ok] using
    full_noop (fun i => poseidon2.Poseidon2RoundKind.ExternalFinal (UScalar.cast .U8 i)) xs s input round

theorem internal_source (iter : PV_RunJoin_SourceInternalRounds.Iter)
    (xs : List (Usize × U32))
    (ht : BuilderStdModels.FiniteTrace PV_RunJoin_SourceInternalRounds.iterator iter xs)
    (s input : State) (round : U8) (hs : Canonical s)
    (hc : ∀ p ∈ xs, p.2.val < 2147483647) :
    (do
      let p ← poseidon2.permute_optimized_with_trace_loop1 callback iter s () round input
      ok p.1) = internal xs s := by
  rw [PV_RunJoin_SourceInternalRounds.source callback iter xs ht s input () round hs hc]
  exact internal_noop xs s input round

#print axioms initial_source
#print axioms final_source
#print axioms internal_source
#print axioms callback_eq
#print axioms full_noop
#print axioms internal_noop
end R1Z.PV_RunJoin_ParentNoopRounds
