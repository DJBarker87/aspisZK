import R1Z.PV_W_OsFile
set_option autoImplicit false
namespace R1Z.PV_W_FileDecode
open PV_W_Threading PV_RunJoin_OsWorld PV_W_OsFile
variable {E File Reply Time Worker Fs Allocator Extra C A : Type} [DecidableEq File]

/-- Value-decoder DATA. Its native representation/errno/purity association
is still a P obligation. In the model, decoding never rolls back the syscall. -/
def decoded (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (request : Request File) (decode : Reply → Outcome Fault A) :
    M (Full E File Reply Time Worker Fs Allocator Extra) C Fault A :=
  PV_W_Threading.bind (file update tag request) (fun reply => PV_W_Threading.lift (decode reply))

theorem decoded_matched (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (request : Request File) (decode : Reply → Outcome Fault A)
    (w : Full E File Reply Time Worker Fs Allocator Extra)
    (reply : Reply) (next : World E File Reply Time Worker)
    (matched : fileStep request w.os = some (reply,next)) :
    decoded update tag request decode w =
      ⟨decode reply,afterFile update request reply w next,[(w,tag request reply next)]⟩ := by
  simp only [decoded,PV_W_Threading.bind,file_matched update tag request w reply next matched,
    PV_W_Threading.lift,List.append_nil]

theorem decoded_rejected (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (request : Request File) (decode : Reply → Outcome Fault A)
    (w : Full E File Reply Time Worker Fs Allocator Extra)
    (mismatch : fileStep request w.os = none) :
    decoded update tag request decode w = ⟨.fail .fileTape,w,[]⟩ := by
  simp only [decoded,PV_W_Threading.bind,file_rejected update tag request w mismatch]

theorem decoded_valid (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (request : Request File) (decode : Reply → Outcome Fault A) :
    Valid (Step update tag) (decoded update tag request decode) :=
  valid_bind _ _ _ (file_valid update tag request) (fun reply => valid_lift _ (decode reply))

/-- Even a decoder failure or divergence retains the already performed file
transition and its exact pre-world tag. No post-error rollback is inferred. -/
theorem decoded_effect_prefix (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (request : Request File) (decode : Reply → Outcome Fault A)
    (w : Full E File Reply Time Worker Fs Allocator Extra)
    (reply : Reply) (next : World E File Reply Time Worker)
    (matched : fileStep request w.os = some (reply,next)) :
    (decoded update tag request decode w).world = afterFile update request reply w next ∧
    (decoded update tag request decode w).calls = [(w,tag request reply next)] := by
  rw [decoded_matched update tag request decode w reply next matched]
  exact ⟨rfl,rfl⟩

#print axioms decoded_matched
#print axioms decoded_rejected
#print axioms decoded_valid
#print axioms decoded_effect_prefix
end R1Z.PV_W_FileDecode
