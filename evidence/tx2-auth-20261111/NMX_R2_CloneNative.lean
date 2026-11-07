import NMX_R2_ObserveResult
import NMX_R2_AllocationSound
import NMX_ErrorCloneCut
set_option autoImplicit false
noncomputable section
namespace NMX_R2_CloneNative
open Aeneas Aeneas.Std Result AdapterRw NMX_R2_Carrier
/-- The std clone has one allocation site exactly for a nonempty String.
The allocator's abort indicator does not select a child reply or a success
class. Its failure reason is unobservable; only the event prefix survives. -/
def clone (aborts : Bool) (failure : Error) (e : solana_program_error.ProgramError) :
 Result solana_program_error.ProgramError :=
 if aborts && (error e).cloneAllocates then .fail failure else ok e

def install (base : Ops) (aborts : Bool) (failure : Error) : Ops :=
 {base with op35 := clone aborts failure}

theorem clone_return (aborts : Bool) (failure : Error) (e : solana_program_error.ProgramError)
 (plain : (error e).cloneAllocates = false) : clone aborts failure e = ok e := by
 simp only [clone,plain,Bool.and_false,Bool.false_eq_true,if_false]

theorem data_shape (base : Ops) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 r1_pool_adapter.owned.OwnedAccount.data (install base aborts failure) a =
 match a.bytes with
 | .Ok v => ok (.Ok v.deref)
 | .Err e => if aborts && (error e).cloneAllocates then .fail failure else ok (.Err e) := by
 cases h : a.bytes with
 | Ok v => simp only [r1_pool_adapter.owned.OwnedAccount.data,h]
 | Err e =>
   rw [NMX_ErrorCloneCut.data_error _ _ e h]
   change ((do let copied ← clone aborts failure e; ok (.Err copied)) :
    Result (core.result.Result (Slice U8) solana_program_error.ProgramError)) =
    (if aborts && (error e).cloneAllocates then .fail failure else ok (.Err e))
   unfold clone
   cases flag : (aborts && (error e).cloneAllocates) <;>
    simp only [flag,Bool.false_eq_true,↓reduceIte,bind_tc_fail,bind_tc_ok]

/-- The actual emitted getter, including its allocating error-clone arm,
satisfies the revision2 getter for every OwnedAccount, without SnapshotErrs. -/
theorem data (base : Ops) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) (env : RSL.Env) :
 RSL.OwnedAccount.data (account a) env
 (NMX_R2_ObserveResult.observe bytes
  (r1_pool_adapter.owned.OwnedAccount.data (install base aborts failure) a)) := by
 rw [data_shape]
 change RSL.RS.ofCloned (reply (fun v => v.val.map byte) a.bytes) env _
 cases h : a.bytes with
 | Ok v => rfl
 | Err e =>
   change RSL.RS.ofCloned (.error (error e)) env
    (NMX_R2_ObserveResult.observe bytes
     (if aborts && (error e).cloneAllocates then .fail failure else ok (.Err e)))
   cases allocates : (error e).cloneAllocates with
   | false => simp only [RSL.RS.ofCloned,allocates,Bool.and_false,Bool.false_eq_true,if_false]; rfl
   | true =>
     simp only [RSL.RS.ofCloned,allocates,Bool.and_true,↓reduceIte]
     cases aborts with
     | false =>
       exact Or.inl ⟨.ok (),[],⟨.ret (.error (error e)),[]⟩,
        Or.inl ⟨(),[],⟨.ret (.ok ()),[]⟩,Or.inl rfl,rfl,rfl⟩,rfl,rfl⟩
     | true =>
       exact Or.inr (Or.inl ⟨[],Or.inr (Or.inl ⟨[],Or.inr rfl,rfl⟩),rfl⟩)
#print axioms clone_return
#print axioms data_shape
#print axioms data
end NMX_R2_CloneNative
end
