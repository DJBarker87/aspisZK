import DotPushWordSource
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1DotPushLocal.Proof

private theorem ix0 (a b c d : U64) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
private theorem ix1 (a b c d : U64) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
private theorem ix2 (a b c d : U64) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
private theorem ix3 (a b c d : U64) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl
private theorem up0 (a b c d x : U64) : Array.update (Array.make 4#usize [a,b,c,d]) 0#usize x = .ok (Array.make 4#usize [x,b,c,d]) := rfl
private theorem up1 (a b c d x : U64) : Array.update (Array.make 4#usize [a,b,c,d]) 1#usize x = .ok (Array.make 4#usize [a,x,c,d]) := rfl
private theorem up2 (a b c d x : U64) : Array.update (Array.make 4#usize [a,b,c,d]) 2#usize x = .ok (Array.make 4#usize [a,b,x,d]) := rfl
private theorem up3 (a b c d x : U64) : Array.update (Array.make 4#usize [a,b,c,d]) 3#usize x = .ok (Array.make 4#usize [a,b,c,x]) := rfl
private theorem shift31 (r : U64) : r >>> 31#i32 = .ok (AspisR1.EbyKDotPushCanonicalFoldBridgeV1.high r) := rfl

theorem push_four_coordinates
    (rawFn : canonical.Q → canonical.Q → Result (Array U64 4#usize))
    (left right : canonical.Q) (a b c d r0 r1 r2 r3 : U64)
    (hraw : rawFn left right = .ok (Array.make 4#usize [r0,r1,r2,r3])) :
    canonical.Dot.push rawFn ⟨Array.make 4#usize [a,b,c,d]⟩ left right =
      .ok ⟨Array.make 4#usize [updateWord a r0,updateWord b r1,updateWord c r2,updateWord d r3]⟩ := by
  simp only [canonical.Dot.push,hraw,bind_tc_ok,ix0,ix1,ix2,ix3,up0,up1,up2,up3,
    canonical.P,lift,shift31]
  rfl

#print axioms push_four_coordinates
end AspisR1DotPushLocal.Proof
