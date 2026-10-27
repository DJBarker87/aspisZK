import JFn_ScaleTotal
import SAQ_LineSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_LineTotal
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof

theorem source (alpha a b c d : E) (ix iy lx ly lz : U32)
    (hAlpha : CanonicalWide alpha) (ha : CanonicalWide a) (hb : CanonicalWide b)
    (hc : CanonicalWide c) (hd : CanonicalWide d) :
    ∃ out, SAQ_LineSource.line alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out ∧ CanonicalWide out := by
  obtain ⟨we,Hwe,Cwe,_⟩ := wide_add_total_exact a b ha hb
  obtain ⟨we1,Hwe1,Cwe1,_⟩ := wide_add_total_exact we c Cwe hc
  obtain ⟨we2,Hwe2,Cwe2,_⟩ := wide_add_total_exact we1 d Cwe1 hd
  obtain ⟨h0,Hh0,Ch0⟩ := JFn_ScaleTotal.wide we2 SAQ_LineSource.quarter
  obtain ⟨we3,Hwe3,Cwe3,_⟩ := wide_sub_total_exact we c Cwe hc
  obtain ⟨we4,Hwe4,Cwe4,_⟩ := wide_sub_total_exact we3 d Cwe3 hd
  obtain ⟨m,Hm⟩ := JFn_ScaleTotal.base SAQ_LineSource.quarter lz
  obtain ⟨h2,Hh2,Ch2⟩ := JFn_ScaleTotal.wide we4 m
  obtain ⟨we5,Hwe5,Cwe5,_⟩ := wide_sub_total_exact a b ha hb
  obtain ⟨m1,Hm1⟩ := JFn_ScaleTotal.base 1073741824#u32 lx
  obtain ⟨c0,Hc0,Cc0⟩ := JFn_ScaleTotal.wide we5 m1
  obtain ⟨we6,Hwe6,Cwe6,_⟩ := wide_sub_total_exact d c hd hc
  obtain ⟨m2,Hm2⟩ := JFn_ScaleTotal.base 1073741824#u32 ly
  obtain ⟨c1,Hc1,Cc1⟩ := JFn_ScaleTotal.wide we6 m2
  obtain ⟨we7,Hwe7,Cwe7,_⟩ := wide_add_total_exact c0 c1 Cc0 Cc1
  obtain ⟨h1,Hh1,Ch1⟩ := JFn_ScaleTotal.wide we7 1073741824#u32
  obtain ⟨we8,Hwe8,Cwe8,_⟩ := wide_sub_total_exact c0 c1 Cc0 Cc1
  obtain ⟨m3,Hm3⟩ := JFn_ScaleTotal.base 1073741824#u32 lz
  obtain ⟨h3,Hh3,Ch3⟩ := JFn_ScaleTotal.wide we8 m3
  obtain ⟨we9,Hwe9,Cwe9,_⟩ := wide_mul_total_exact alpha h3 hAlpha Ch3
  obtain ⟨we10,Hwe10,Cwe10,_⟩ := wide_add_total_exact h2 we9 Ch2 Cwe9
  obtain ⟨we11,Hwe11,Cwe11,_⟩ := wide_mul_total_exact alpha we10 hAlpha Cwe10
  obtain ⟨we12,Hwe12,Cwe12,_⟩ := wide_add_total_exact h1 we11 Ch1 Cwe11
  obtain ⟨we13,Hwe13,Cwe13,_⟩ := wide_mul_total_exact alpha we12 hAlpha Cwe12
  obtain ⟨out,Hout,Cout,_⟩ := wide_add_total_exact h0 we13 Ch0 Cwe13
  refine ⟨out,?_,Cout⟩
  have ia0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize=ok a := rfl
  have ia1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize=ok b := rfl
  have ia2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize=ok c := rfl
  have ia3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize=ok d := rfl
  have ii2 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 2#usize=ok lx := rfl
  have ii3 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 3#usize=ok ly := rfl
  have ii4 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 4#usize=ok lz := rfl
  simp only [SAQ_LineSource.line,ia0,ia1,ia2,ia3,ii2,ii3,ii4,Hwe,Hwe1,Hwe2,Hh0,Hwe3,Hwe4,Hm,Hh2,Hwe5,Hm1,Hc0,Hwe6,Hm2,Hc1,Hwe7,Hh1,Hwe8,Hm3,Hh3,Hwe9,Hwe10,Hwe11,Hwe12,Hwe13,Hout,bind_tc_ok]

#print axioms source
end AspisR1.JFn_LineTotal
end
