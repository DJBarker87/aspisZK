import R1Z.PV_RunJoin_SuperRootScan30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SuperRootCall30
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestStdPort PV_RunJoin_SuperRootScan30

theorem checked (a : Roots) {s : Slice (Array U32 8#usize)}
    {i : core.slice.iter.Iter (Array U32 8#usize)}
    {f after : BuilderForestStd.Flatten _ _ _ _}
    (hs : lift (Array.to_slice a) = ok s)
    (hi : core.slice.Slice.iter s = ok i)
    (hf : core.iter.traits.iterator.Iterator.flatten.default outer conv i = ok f)
    (ha : core.iter.traits.iterator.Iterator.any.default flat predicate f () = ok (false,after)) :
    ∀ l, l<3 → Canon8 a.val[l]! := by
  change ok (Array.to_slice a) = ok s at hs
  cases Result.ok.inj hs
  change ok (⟨Array.to_slice a,0⟩ : core.slice.iter.Iter (Array U32 8#usize)) = ok i at hi
  cases Result.ok.inj hi
  change ok (⟨⟨Array.to_slice a,0⟩,none⟩ : BuilderForestStd.Flatten _ _ _ _) = ok f at hf
  cases Result.ok.inj hf
  exact scan_false a after ha
#print axioms checked
end R1Z.PV_RunJoin_SuperRootCall30
