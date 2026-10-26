import JFn_ScaleTotal
import FIp_CircleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_CircleTotal
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof

/-- The actual circle arithmetic returns on canonical operands. This is not
the circle-fold equality gate: that requires the computed dot values. -/
theorem source (alpha a b c d : E) (ix iy lx ly lz : U32)
    (hAlpha : CanonicalWide alpha) (ha : CanonicalWide a) (hb : CanonicalWide b)
    (hc : CanonicalWide c) (hd : CanonicalWide d) :
    ∃ out, FIp_CircleSource.circle alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out ∧ CanonicalWide out := by
  obtain ⟨we,Hwe,Cwe,_⟩ := wide_add_total_exact a b ha hb
  obtain ⟨we1,Hwe1,Cwe1,_⟩ := wide_add_total_exact we c Cwe hc
  obtain ⟨we2,Hwe2,Cwe2,_⟩ := wide_add_total_exact we1 d Cwe1 hd
  obtain ⟨h0,Hh0,Ch0⟩ := JFn_ScaleTotal.wide we2 SAQ_LineSource.quarter
  obtain ⟨we3,Hwe3,Cwe3,_⟩ := wide_sub_total_exact a b ha hb
  obtain ⟨we4,Hwe4,Cwe4,_⟩ := wide_sub_total_exact we3 c Cwe3 hc
  obtain ⟨we5,Hwe5,Cwe5,_⟩ := wide_add_total_exact we4 d Cwe4 hd
  obtain ⟨m,Hm⟩ := JFn_ScaleTotal.base SAQ_LineSource.quarter iy
  obtain ⟨h1,Hh1,Ch1⟩ := JFn_ScaleTotal.wide we5 m
  obtain ⟨we6,Hwe6,Cwe6,_⟩ := wide_sub_total_exact we c Cwe hc
  obtain ⟨we7,Hwe7,Cwe7,_⟩ := wide_sub_total_exact we6 d Cwe6 hd
  obtain ⟨m1,Hm1⟩ := JFn_ScaleTotal.base SAQ_LineSource.quarter ix
  obtain ⟨h2,Hh2,Ch2⟩ := JFn_ScaleTotal.wide we7 m1
  obtain ⟨we8,Hwe8,Cwe8,_⟩ := wide_add_total_exact we3 c Cwe3 hc
  obtain ⟨we9,Hwe9,Cwe9,_⟩ := wide_sub_total_exact we8 d Cwe8 hd
  obtain ⟨m2,Hm2⟩ := JFn_ScaleTotal.base m1 iy
  obtain ⟨h3,Hh3,Ch3⟩ := JFn_ScaleTotal.wide we9 m2
  obtain ⟨we10,Hwe10,Cwe10,_⟩ := wide_mul_total_exact alpha h3 hAlpha Ch3
  obtain ⟨we11,Hwe11,Cwe11,_⟩ := wide_add_total_exact h2 we10 Ch2 Cwe10
  obtain ⟨we12,Hwe12,Cwe12,_⟩ := wide_mul_total_exact alpha we11 hAlpha Cwe11
  obtain ⟨we13,Hwe13,Cwe13,_⟩ := wide_add_total_exact h1 we12 Ch1 Cwe12
  obtain ⟨we14,Hwe14,Cwe14,_⟩ := wide_mul_total_exact alpha we13 hAlpha Cwe13
  obtain ⟨out,Hout,Cout,_⟩ := wide_add_total_exact h0 we14 Ch0 Cwe14
  refine ⟨out,?_,Cout⟩
  have ia0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize=ok a := rfl
  have ia1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize=ok b := rfl
  have ia2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize=ok c := rfl
  have ia3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize=ok d := rfl
  have ii0 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 0#usize=ok ix := rfl
  have ii1 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 1#usize=ok iy := rfl
  simp only [FIp_CircleSource.circle,ia0,ia1,ia2,ia3,ii0,ii1,Hwe,Hwe1,Hwe2,Hh0,Hwe3,
    Hwe4,Hwe5,Hm,Hh1,Hwe6,Hwe7,Hm1,Hh2,Hwe8,Hwe9,Hm2,Hh3,Hwe10,Hwe11,Hwe12,Hwe13,
    Hwe14,Hout,bind_tc_ok]

#print axioms source
end AspisR1.JFr_TX2_CircleTotal
end
