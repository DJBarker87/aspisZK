import NMX_R2_AccountReify
set_option autoImplicit false
namespace NMX_R2_AccountListReify
open Aeneas Aeneas.Std

def list : (xs : List RSL.OwnedAccount) → (∀ a ∈ xs, NMX_R2_AccountReify.Bounds a) →
 List AdapterRw.r1_pool_adapter.owned.OwnedAccount
 | [],_ => []
 | a::xs,h => NMX_R2_AccountReify.account a (h a (by simp)) ::
   list xs (fun b hb => h b (by simp only [List.mem_cons]; exact Or.inr hb))

theorem image : ∀ (xs : List RSL.OwnedAccount) (h : ∀ a ∈ xs, NMX_R2_AccountReify.Bounds a),
 (list xs h).map NMX_R2_Carrier.account = xs
 | [],_ => rfl
 | a::xs,h => by
   simp only [list,List.map_cons,NMX_R2_AccountReify.roundtrip]
   exact congrArg (List.cons a) (image xs (fun b hb => h b (by simp only [List.mem_cons]; exact Or.inr hb)))

theorem length (xs : List RSL.OwnedAccount) (h : ∀ a ∈ xs, NMX_R2_AccountReify.Bounds a) :
 (list xs h).length = xs.length := by
 have result := congrArg List.length (image xs h)
 simpa only [List.length_map] using result
#print axioms image
#print axioms length
end NMX_R2_AccountListReify
