import NMX_R2_CloneNative
import NMX_LengthCloneCut
set_option autoImplicit false
noncomputable section
namespace NMX_R2_LengthNative
open Aeneas Aeneas.Std Result AdapterRw NMX_R2_Carrier NMX_R2_CloneNative

theorem shape (base : Ops) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 r1_pool_adapter.owned.OwnedAccount.data_len (install base aborts failure) a =
 match a.length with
 | .Ok n => ok (.Ok n)
 | .Err e => if aborts && (error e).cloneAllocates then .fail failure else ok (.Err e) := by
 rw [NMX_LengthCloneCut.shape]
 cases h : a.length with
 | Ok n => rfl
 | Err e =>
   change ((do let copied ← clone aborts failure e; ok (.Err copied)) :
    Result (core.result.Result (Usize) solana_program_error.ProgramError)) =
    (if aborts && (error e).cloneAllocates then .fail failure else ok (.Err e))
   unfold clone
   cases flag : (aborts && (error e).cloneAllocates) <;>
    simp only [flag,Bool.false_eq_true,↓reduceIte,bind_tc_fail,bind_tc_ok]

theorem length (base : Ops) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) (env : RSL.Env) :
 RSL.OwnedAccount.data_len (account a) env
 (NMX_R2_ObserveResult.observe (fun n : Usize => n.val)
  (r1_pool_adapter.owned.OwnedAccount.data_len (install base aborts failure) a)) := by
 rw [shape]
 change RSL.RS.ofCloned (reply (fun n : Usize => n.val) a.length) env _
 cases h : a.length with
 | Ok v => rfl
 | Err e =>
   change RSL.RS.ofCloned (.error (error e)) env
    (NMX_R2_ObserveResult.observe (fun n : Usize => n.val)
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
#print axioms shape
#print axioms length
end NMX_R2_LengthNative
end
