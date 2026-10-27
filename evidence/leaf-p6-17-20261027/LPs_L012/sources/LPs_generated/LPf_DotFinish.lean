import LPf_ReductionWord
set_option autoImplicit false
namespace AspisR1.LPf_DotFinish
open Aeneas Aeneas.Std Result

/-- Compose four unconditional reducer results in the actual extracted private
Dot::finish body. The four input words are independent and unrestricted. -/
theorem source (a b c d : U64) : ∃ z0 z1 z2 z3,
    FIo_Native.fast_pairing.canonical.Dot.finish
      ⟨Array.make 4#usize [a,b,c,d]⟩ = ok (Array.make 4#usize [z0,z1,z2,z3]) ∧
    z0.val = a.val % 2147483647 ∧ z1.val = b.val % 2147483647 ∧
    z2.val = c.val % 2147483647 ∧ z3.val = d.val % 2147483647 ∧
    z0.val < 2147483647 ∧ z1.val < 2147483647 ∧
    z2.val < 2147483647 ∧ z3.val < 2147483647 := by
  obtain ⟨z0,h0,v0,c0⟩ := LPf_ReductionWord.native_reduce a
  obtain ⟨z1,h1,v1,c1⟩ := LPf_ReductionWord.native_reduce b
  obtain ⟨z2,h2,v2,c2⟩ := LPf_ReductionWord.native_reduce c
  obtain ⟨z3,h3,v3,c3⟩ := LPf_ReductionWord.native_reduce d
  refine ⟨z0,z1,z2,z3,?_,v0,v1,v2,v3,c0,c1,c2,c3⟩
  have i0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = ok a := rfl
  have i1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = ok b := rfl
  have i2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = ok c := rfl
  have i3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = ok d := rfl
  simp only [FIo_Native.fast_pairing.canonical.Dot.finish,i0,i1,i2,i3,
    bind_tc_ok,h0,h1,h2,h3]

#print axioms source
end AspisR1.LPf_DotFinish
