import NDG_AccessLaws
import NDG_ReferenceExtra.Funs
set_option autoImplicit false
namespace NDG_IdentityLaws
open Aeneas Aeneas.Std Result AdapterRw

theorem data_reference (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
    (v : alloc.vec.Vec U8) (h : a.bytes = .Ok v) :
    (do let s ← NDG_ReferenceExtra.data_ref (alloc.vec.Vec.deref v)
        ok (core.result.Result.Ok s)) = r1_pool_adapter.owned.OwnedAccount.data ops a := by
  exact (NDG_AccessLaws.data_success ops a v h).symm

theorem length_success (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
    (n : Usize) (h : a.length = .Ok n) :
    r1_pool_adapter.owned.OwnedAccount.data_len ops a =
      (do let v ← NDG_ReferenceExtra.length_ref n
          ok (core.result.Result.Ok v)) := by
  simp [r1_pool_adapter.owned.OwnedAccount.data_len, h,
    core.result.Result.Insts.CoreCloneClone.clone, NDG_ReferenceExtra.length_ref]

def installIds (ops : Ops) : Ops :=
  {ops with op45 := NDG_Reference.pool_id_ref, op46 := NDG_Reference.registry_id_ref}

theorem pool_slot (ops : Ops) : (installIds ops).op45 = NDG_Reference.pool_id_ref := rfl

theorem registry_slot (ops : Ops) : (installIds ops).op46 = NDG_Reference.registry_id_ref := rfl

theorem unrelated_digest (ops : Ops) : (installIds ops).op43 = ops.op43 := rfl

/-- Functional list induction: the native arbitrary byte window needs a separate
    step association before this value law can justify the whole native loop. -/
def allZero : List U8 → Bool
 | [] => true
 | x::xs => if x = 0#u8 then allZero xs else false

theorem allZero_iff (xs : List U8) : allZero xs = true ↔ ∀ x ∈ xs, x = 0#u8 := by
  induction xs with
  | nil => simp [allZero]
  | cons x xs ih =>
    by_cases h : x = 0#u8 <;> simp [allZero, h, ih]

theorem zero_step_reference (x : U8) :
    NDG_ReferenceExtra.zero_step_ref x = ok (decide (x = 0#u8)) := rfl

#print axioms data_reference
#print axioms length_success
#print axioms pool_slot
#print axioms registry_slot
#print axioms unrelated_digest
#print axioms allZero_iff
#print axioms zero_step_reference
end NDG_IdentityLaws
