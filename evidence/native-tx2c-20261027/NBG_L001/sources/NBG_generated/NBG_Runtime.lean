import NBC_Audit
set_option autoImplicit false
noncomputable section
namespace NBG_Runtime
open Aeneas Aeneas.Std Result

/-- The wrapper retains the actual syscall transition, including its ordered
observable state; digest realization remains the approved runtime trust row. -/
def digest {State : Type} (hashv : NBC_ReleaseLeaves.Parts → State →
    Result (NBC_ReleaseLeaves.Digest × State))
    (parts : NBC_ReleaseLeaves.Parts) (state : State) :
    Result (NBC_ReleaseLeaves.Digest × State) := do
  let (reply, after) ← hashv parts state
  let out ← NBC_ReleaseLeaves.toBytes reply
  ok (out, after)

theorem digest_transition {State : Type}
    (hashv : NBC_ReleaseLeaves.Parts → State → Result (NBC_ReleaseLeaves.Digest × State))
    (parts : NBC_ReleaseLeaves.Parts) (state : State) :
    digest hashv parts state = hashv parts state := by
  cases h : hashv parts state with
  | ok out => cases out; simp only [digest, h, NBC_ReleaseLeaves.toBytes, bind_tc_ok]
  | fail error => simp only [digest, h, bind_tc_fail]
  | div => simp only [digest, h, bind_tc_div]

#print axioms digest_transition
end NBG_Runtime
