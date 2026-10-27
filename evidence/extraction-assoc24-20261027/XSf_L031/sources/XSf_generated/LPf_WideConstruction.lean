import LPf_ReductionWord
set_option autoImplicit false
namespace AspisR1.LPf_WideConstruction
open Aeneas Aeneas.Std Result
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact

def value (a b c d e f g h : U32) : E :=
  ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩

theorem source (a b c d e f g h : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (he : e.val < 2147483647) (hf : f.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [a,b,c,d,e,f,g,h]) = ok (some (value a b c d e f g h)) := by
  have i0 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 0#usize = ok a := rfl
  have i1 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 1#usize = ok b := rfl
  have i2 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 2#usize = ok c := rfl
  have i3 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 3#usize = ok d := rfl
  have i4 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 4#usize = ok e := rfl
  have i5 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 5#usize = ok f := rfl
  have i6 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 6#usize = ok g := rfl
  have i7 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 7#usize = ok h := rfl
  have na : ¬a ≥ 2147483647#u32 := by scalar_tac
  have nb : ¬b ≥ 2147483647#u32 := by scalar_tac
  have nc : ¬c ≥ 2147483647#u32 := by scalar_tac
  have nd : ¬d ≥ 2147483647#u32 := by scalar_tac
  have ne : ¬e ≥ 2147483647#u32 := by scalar_tac
  have nf : ¬f ≥ 2147483647#u32 := by scalar_tac
  have ng : ¬g ≥ 2147483647#u32 := by scalar_tac
  have nh : ¬h ≥ 2147483647#u32 := by scalar_tac
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
    i0,i1,i2,i3,i4,i5,i6,i7,bind_tc_ok,FIo_Native.aspis_core.field.P,
    if_neg na,if_neg nb,if_neg nc,if_neg nd,if_neg ne,if_neg nf,if_neg ng,if_neg nh] <;> rfl

#print axioms source
end AspisR1.LPf_WideConstruction
