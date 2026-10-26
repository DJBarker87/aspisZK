import R1Z.PV_L2_F3FullSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3PrefixBounds
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R1Z.ProverCommitStepLoop (State Hash)
open R1Z.PV_L2_F3FullSource
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- No whole-source success assumption: allocation/hash failure, exhaustion
and rejected candidates all satisfy the same finite prefix bound. -/
theorem read_bound (hash : Hash) (domain : Slice U8) (L r : Nat) (state : State) :
    (produce (K := K) hash domain L r state).2.length ≤ 16*L+r := by
  fun_induction produce (K := K) hash domain L r state <;>
    simp_all +zetaDelta only [List.length_cons,List.length_nil] <;> omega

theorem actual_answers (hash : Hash) (domain : Slice U8) (L r : Nat) (state : State) :
    ∀ read ∈ (produce (K := K) hash domain L r state).2,
      read.answer = prover_commit_reference.next hash domain read.before := by
  fun_induction produce (K := K) hash domain L r state <;>
    simp_all +zetaDelta only [List.mem_cons,List.not_mem_nil,false_implies,
      forall_const,forall_eq_or_imp]

theorem request_bound (hash : Hash) (domain : Slice U8) (L r : Nat) (state : State) :
    (requests domain (produce (K := K) hash domain L r state).2).length ≤ 16*L+r := by
  exact (List.length_filterMap_le _ _).trans (read_bound hash domain L r state)

theorem failed_read (hash : Hash) (domain : Slice U8) (L r : Nat) (state : State)
    (error : Aeneas.Std.Error)
    (failure : prover_commit_reference.next hash domain state = .fail error) :
    produce (K := K) hash domain (L+1) (r+1) state =
      (none,[⟨state,.fail error⟩]) := by
  rw [produce,failure]

theorem diverging_read (hash : Hash) (domain : Slice U8) (L r : Nat) (state : State)
    (failure : prover_commit_reference.next hash domain state = .div) :
    produce (K := K) hash domain (L+1) (r+1) state = (none,[⟨state,.div⟩]) := by
  rw [produce,failure]

theorem exhausted (hash : Hash) (domain : Slice U8) (L : Nat) (state : State) :
    produce (K := K) hash domain (L+1) 0 state = (none,[]) := rfl

#print axioms read_bound
#print axioms actual_answers
#print axioms request_bound
#print axioms failed_read
#print axioms diverging_read
#print axioms exhausted
end R1Z.PV_L2_F3PrefixBounds
