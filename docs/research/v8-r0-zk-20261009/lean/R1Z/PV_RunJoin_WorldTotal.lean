import R1Z.PV_RunJoin_EntropyCapacity

/-! Total finite-carrier prototype execution. An arbitrary adaptive nonce
policy reads the advancing provider; this is not the native account callback.
Every entropy status, including OS errors, is retained in the replay. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WorldTotal
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerEvents ProverRwRngOwnerInventory PV_RunJoin_World
variable [ErasureFns]

abbrev Policy := Nat → Tape → Array U8 32#usize

/-- The first call has index zero. The next policy receives the exact returned
provider even when the preceding entropy status was an OS error. The actual
native prover may stop earlier; this relation is a capacity completion. -/
inductive PolicyReplay (policy : Policy) : Nat → Tape → List (List State) → Tape → Prop
  | nil (index : Nat) (p : Tape) : PolicyReplay policy index p [] p
  | cons {index : Nat} {p next final : Tape} {states : List State} {rest : List (List State)}
      (status : ProverRwRngControl.Status)
      (run : owner (policy index p) p = .ok (next,status))
      (trace : OwnerReplay (newBody (policy index p)) id (policy index p) p states (next,status))
      (tail : PolicyReplay policy (index+1) next rest final) :
      PolicyReplay policy index p (states :: rest) final

theorem replay_owners {policy : Policy} {index : Nat} {p final : Tape}
    {calls : List (List State)} (run : PolicyReplay policy index p calls final) :
    Owners p calls final := by
  induction run with
  | nil index p => exact .nil p
  | cons status run trace tail ih => exact .cons _ status run trace ih

/-- No extraction-success premise. Sufficient capacity supplies a full replay
for arbitrary bytes, OS-error tags, nonces, and adaptive nonce policies. -/
theorem policy_total (policy : Policy) (n : Nat) (index : Nat) (p : Tape)
    (capacity : p.used.val + 16*n ≤ p.replies.val.length) :
    ∃ final calls, PolicyReplay policy index p calls final ∧ calls.length = n := by
  induction n generalizing index p with
  | zero => exact ⟨p,[],.nil index p,rfl⟩
  | succ n ih =>
    have firstCapacity : p.used.val + 16 ≤ p.replies.val.length := by omega
    obtain ⟨next,status,run⟩ := PV_RunJoin_EntropyCapacity.owner_total (policy index p) p firstCapacity
    obtain ⟨states,_,trace,_,_,_,_,_,_⟩ :=
      (ProverRwRngOwnerCertificate.universal_cap16 (policy index p) p).2 next status run
    obtain ⟨same,cursor,bound,_⟩ := owner_inventory trace
    have nextCapacity : next.used.val + 16*n ≤ next.replies.val.length := by
      rw [same,cursor]
      omega
    obtain ⟨final,rest,tail,length⟩ := ih (index+1) next nextCapacity
    exact ⟨final,states::rest,.cons status run trace tail,by simp only [List.length_cons,length]⟩

/-- A full eight-call completion exists on EVERY finite raw tape. Native
early-stop/error handling must still be associated separately. No uniformity
law or complete prover/source equation is asserted. -/
theorem cap8_total (raw : RawTape) (policy : Policy) :
    ∃ final calls,
      PolicyReplay policy 0 (provider raw 0#usize) calls final ∧
      calls.length = 8 ∧ final.replies.val = replies raw ∧
      final.used.val = count calls ∧ count calls ≤ 128 ∧
      log calls = (List.range' 0 (count calls)).map
        (fun index => (Array.repeat 64#usize 0#u8,index,(replies raw)[index]?)) ∧
      final.replies.val.drop final.used.val = (replies raw).drop (count calls) := by
  have capacity : (provider raw 0#usize).used.val + 16*8 ≤
      (provider raw 0#usize).replies.val.length := by
    change 0+16*8 ≤ (replies raw).length
    rw [replies_length]
  obtain ⟨final,calls,run,length⟩ := policy_total policy 8 0 (provider raw 0#usize) capacity
  exact ⟨final,calls,run,length,
    cap8_inventory raw (replay_owners run) (by omega)⟩

#print axioms replay_owners
#print axioms policy_total
#print axioms cap8_total
end R1Z.PV_RunJoin_WorldTotal
