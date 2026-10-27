import LPf_DotFinish
import LPf_WideConstruction
set_option autoImplicit false
namespace AspisR1.LPf_PublicDotFinish
open Aeneas Aeneas.Std Result

/-- Both halves, the actual finalizer and its checked canonical constructor
compose on one supplied native state. Count is unrestricted and is not read. -/
theorem source (a b c d e f g h : U64) (count : Usize) : ∃ out,
    FIo_Native.fast_pairing.EbyKDot.finish
      ⟨⟨Array.make 4#usize [a,b,c,d]⟩,⟨Array.make 4#usize [e,f,g,h]⟩,count⟩ = ok out ∧
    out.c0.c0.a.val = a.val % 2147483647 ∧ out.c0.c0.b.val = b.val % 2147483647 ∧
    out.c0.c1.a.val = c.val % 2147483647 ∧ out.c0.c1.b.val = d.val % 2147483647 ∧
    out.c1.c0.a.val = e.val % 2147483647 ∧ out.c1.c0.b.val = f.val % 2147483647 ∧
    out.c1.c1.a.val = g.val % 2147483647 ∧ out.c1.c1.b.val = h.val % 2147483647 := by
  obtain ⟨a0,b0,c0,d0,r0,va,vb,vc,vd,ca,cb,cc,cd⟩ := LPf_DotFinish.source a b c d
  obtain ⟨e0,f0,g0,h0,r1,ve,vf,vg,vh,ce,cf,cg,ch⟩ := LPf_DotFinish.source e f g h
  have construct := LPf_WideConstruction.source a0 b0 c0 d0 e0 f0 g0 h0 ca cb cc cd ce cf cg ch
  let out := LPf_WideConstruction.value a0 b0 c0 d0 e0 f0 g0 h0
  refine ⟨out,?_,va,vb,vc,vd,ve,vf,vg,vh⟩
  have i0 (w x y z : U32) : Array.index_usize (Array.make 4#usize [w,x,y,z]) 0#usize = ok w := rfl
  have i1 (w x y z : U32) : Array.index_usize (Array.make 4#usize [w,x,y,z]) 1#usize = ok x := rfl
  have i2 (w x y z : U32) : Array.index_usize (Array.make 4#usize [w,x,y,z]) 2#usize = ok y := rfl
  have i3 (w x y z : U32) : Array.index_usize (Array.make 4#usize [w,x,y,z]) 3#usize = ok z := rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.finish,r0,r1,
    FIo_Native.fast_pairing.canonical.Q.limbs,bind_tc_ok,i0,i1,i2,i3,construct] <;> rfl

#print axioms source
end AspisR1.LPf_PublicDotFinish
