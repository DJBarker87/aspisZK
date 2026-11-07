import NNH_AuthNativeFission
set_option autoImplicit false
namespace NNH_SevenAccounts
open Aeneas Aeneas.Std AdapterRw

def value (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) : Slice r1_pool_adapter.owned.OwnedAccount :=
 Array.to_slice (Array.make 7#usize [p,m,c,l,r,e,v])

theorem length (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) :
 Slice.len (value p m c l r e v)=7#usize := by rfl

theorem indices (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) :
 Slice.index_usize (value p m c l r e v) 0#usize=.ok p ∧
 Slice.index_usize (value p m c l r e v) 1#usize=.ok m ∧
 Slice.index_usize (value p m c l r e v) 2#usize=.ok c ∧
 Slice.index_usize (value p m c l r e v) 3#usize=.ok l ∧
 Slice.index_usize (value p m c l r e v) 4#usize=.ok r ∧
 Slice.index_usize (value p m c l r e v) 5#usize=.ok e ∧
 Slice.index_usize (value p m c l r e v) 6#usize=.ok v := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms length
#print axioms indices
end NNH_SevenAccounts
