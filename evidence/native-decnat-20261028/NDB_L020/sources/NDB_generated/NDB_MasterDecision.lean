import NDB_SequenceDecision
set_option autoImplicit false
namespace NDB_MasterDecision
open Aeneas Aeneas.Std Result

def outcome (m : NCV_Reference.Master) (pool mint token domain policy valid zero : Bool) : Bool :=
  !pool && !mint && !token && !domain && policy && valid &&
    (if m.has_checkpoint then !(m.next_checkpoint_sequence=0#u64)
     else (m.next_checkpoint_sequence=0#u64) && zero)

theorem value (m : NCV_Reference.Master) (pool mint token domain policy valid zero : Bool)
    (p : NCV_Reference.zero (Array.to_slice m.identity.pool)=ok pool)
    (a : NCV_Reference.zero (Array.to_slice m.identity.asset_mint)=ok mint)
    (t : NCV_Reference.zero (Array.to_slice m.identity.token_program)=ok token)
    (d : NCV_Reference.zero (Array.to_slice m.identity.deployment_domain)=ok domain)
    (v : NCV_Reference.valid_policy m.verifier_policy=ok policy)
    (s : NCV_Reference.valid_sequences m.last_checkpoint_lane_sequences=ok valid)
    (z : NCV_Reference.zero_sequences m.last_checkpoint_lane_sequences=ok zero) :
    NCV_Reference.valid_master m=ok (outcome m pool mint token domain policy valid zero) := by
  simp only [NCV_Reference.valid_master,lift,bind_tc_ok,p,a,t,d,v,s,z]
  cases pool <;> cases mint <;> cases token <;> cases domain <;> cases policy <;>
    cases valid <;> cases zero <;> cases h : m.has_checkpoint <;>
    by_cases next : m.next_checkpoint_sequence=0#u64 <;>
    simp [outcome,next,h]
#print axioms value
end NDB_MasterDecision
