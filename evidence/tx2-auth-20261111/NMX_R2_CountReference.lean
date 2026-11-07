import NMX_R2_CanonicalTarget
set_option autoImplicit false
namespace NMX_R2_CountReference
open RSL
/-- The rejected count arm calls no child or allocator. -/
theorem other (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (count : a.accounts.length ≠ 7) :
 TX2_233.Ref L D a = RS.throw
  (if a.accounts.length < 7 then .notEnoughAccountKeys else .invalidArgument) := by
 unfold TX2_233.Ref
 split
 · rename_i p m c l r e v shape
   exact False.elim (count (by simp only [shape,List.length_cons,List.length_nil]))
 · rfl
#print axioms other
end NMX_R2_CountReference
