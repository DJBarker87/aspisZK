import R1Z.PV_RDB2C_V259
namespace R1Z.PV_RDB2C_BoxAdequacy
open R1Z.PV_RDB2C_PublicRequests R1Z.PV_RDB2C_Box

/-- The retained runtime/allocator primitive adequacy law, stated at the
actual typed-object allocation boundary. Logical-object frame theorems alone
do not prove byte ranges disjoint or establish a valid Rust pointer. -/
def Adequate {T S : Type} (allocate : Request → S → Option Nat × S)
    (request : Request) (world : World T S) : Prop :=
  ∀ p state, allocate request world.allocator=(some p,state) →
    p≠0 ∧ p%request.alignment=0 ∧
    ∀ a, world.live a=true → a+request.size≤p ∨ p+request.size≤a

theorem initialized_fresh_aligned {T S : Type}
    (allocate : Request → S → Option Nat × S) (request : Request)
    (value : T) (world : World T S) (p : Nat) (state : S)
    (primitive_adequacy : Adequate allocate request world)
    (h : allocate request world.allocator=(some p,state)) :
    p≠0 ∧ p%request.alignment=0 ∧
    (lowered allocate request value world).2.objects p=some value ∧
    (∀ a, world.live a=true → a+request.size≤p ∨ p+request.size≤a) := by
  obtain ⟨nonnull,aligned,fresh⟩ := primitive_adequacy p state h
  exact ⟨nonnull,aligned,(initialized allocate request value world p state h).1,fresh⟩

theorem failure_has_no_initialization {T S : Type}
    (allocate : Request → S → Option Nat × S) (request : Request)
    (value : T) (world : World T S) (state : S)
    (h : allocate request world.allocator=(none,state)) :
    (lowered allocate request value world).2.objects=world.objects ∧
    (lowered allocate request value world).2.live=world.live := by
  simp only [lowered,h]

#print axioms initialized_fresh_aligned
#print axioms failure_has_no_initialization
end R1Z.PV_RDB2C_BoxAdequacy
