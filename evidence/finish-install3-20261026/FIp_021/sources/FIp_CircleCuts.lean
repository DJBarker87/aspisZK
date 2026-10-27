import FIp_CircleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_CircleCuts
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof
structure Cuts (alpha a b c d : E) (ix iy : U32) (out : E) where
  we : E
  we1 : E
  we2 : E
  h0 : E
  we3 : E
  we4 : E
  we5 : E
  m : U32
  h1 : E
  we6 : E
  we7 : E
  m1 : U32
  h2 : E
  we8 : E
  we9 : E
  m2 : U32
  h3 : E
  we10 : E
  we11 : E
  we12 : E
  we13 : E
  we14 : E
  Hwe : field.wide_exact.WideExact.add a b=ok we
  Hwe1 : field.wide_exact.WideExact.add we c=ok we1
  Hwe2 : field.wide_exact.WideExact.add we1 d=ok we2
  Hh0 : field.wide_exact.WideExact.mul_m31 we2 SAQ_LineSource.quarter=ok h0
  Hwe3 : field.wide_exact.WideExact.sub a b=ok we3
  Hwe4 : field.wide_exact.WideExact.sub we3 c=ok we4
  Hwe5 : field.wide_exact.WideExact.add we4 d=ok we5
  Hm : field.M31.mul SAQ_LineSource.quarter iy=ok m
  Hh1 : field.wide_exact.WideExact.mul_m31 we5 m=ok h1
  Hwe6 : field.wide_exact.WideExact.sub we c=ok we6
  Hwe7 : field.wide_exact.WideExact.sub we6 d=ok we7
  Hm1 : field.M31.mul SAQ_LineSource.quarter ix=ok m1
  Hh2 : field.wide_exact.WideExact.mul_m31 we7 m1=ok h2
  Hwe8 : field.wide_exact.WideExact.add we3 c=ok we8
  Hwe9 : field.wide_exact.WideExact.sub we8 d=ok we9
  Hm2 : field.M31.mul m1 iy=ok m2
  Hh3 : field.wide_exact.WideExact.mul_m31 we9 m2=ok h3
  Hwe10 : field.wide_exact.WideExact.mul alpha h3=ok we10
  Hwe11 : field.wide_exact.WideExact.add h2 we10=ok we11
  Hwe12 : field.wide_exact.WideExact.mul alpha we11=ok we12
  Hwe13 : field.wide_exact.WideExact.add h1 we12=ok we13
  Hwe14 : field.wide_exact.WideExact.mul alpha we13=ok we14
  Hout : field.wide_exact.WideExact.add h0 we14=ok out

theorem cuts (alpha a b c d out : E) (ix iy lx ly lz : U32)
    (run : FIp_CircleSource.circle alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out) :
    Nonempty (Cuts alpha a b c d ix iy out) := by
  have ia0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize=ok a := rfl
  have ia1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize=ok b := rfl
  have ia2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize=ok c := rfl
  have ia3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize=ok d := rfl
  have ii0 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 0#usize=ok ix := rfl
  have ii1 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 1#usize=ok iy := rfl
  simp only [FIp_CircleSource.circle,ia0,ia1,ia2,ia3,ii0,ii1,bind_tc_ok] at run
  obtain ⟨we,Hwe,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we1,Hwe1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we2,Hwe2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨h0,Hh0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we3,Hwe3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we4,Hwe4,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we5,Hwe5,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m,Hm,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨h1,Hh1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we6,Hwe6,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we7,Hwe7,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m1,Hm1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨h2,Hh2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we8,Hwe8,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we9,Hwe9,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m2,Hm2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨h3,Hh3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we10,Hwe10,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we11,Hwe11,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we12,Hwe12,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we13,Hwe13,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we14,Hwe14,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact ⟨⟨we,we1,we2,h0,we3,we4,we5,m,h1,we6,we7,m1,h2,we8,we9,m2,h3,we10,we11,we12,we13,we14,Hwe,Hwe1,Hwe2,Hh0,Hwe3,Hwe4,Hwe5,Hm,Hh1,Hwe6,Hwe7,Hm1,Hh2,Hwe8,Hwe9,Hm2,Hh3,Hwe10,Hwe11,Hwe12,Hwe13,Hwe14,run⟩⟩

#print axioms cuts
end AspisR1.FIp_CircleCuts
end
