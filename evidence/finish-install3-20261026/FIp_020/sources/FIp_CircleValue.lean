import FIp_CircleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_CircleValue
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof
open SAQ_LineSource

def formula (alpha a b c d : AspisWideTower.WideExact) (ix iy : FP) :=
  let embed := algebraMap FP AspisWideTower.WideExact
  let h0 := (a+b+c+d)*embed R1ZCircleFoldMathV1.rustQuarter
  let h1 := (a-b-c+d)*embed (R1ZCircleFoldMathV1.rustQuarter*iy)
  let h2 := (a+b-c-d)*embed (R1ZCircleFoldMathV1.rustQuarter*ix)
  let h3 := (a-b+c-d)*embed (R1ZCircleFoldMathV1.rustQuarter*ix*iy)
  h0+alpha*(h1+alpha*(h2+alpha*h3))

theorem made (alpha a b c d out : E) (ix iy lx ly lz : U32)
    (run : FIp_CircleSource.circle alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out) :
    CanonicalWide out ∧ decodeWide out=formula (decodeWide alpha)
      (decodeWide a) (decodeWide b) (decodeWide c) (decodeWide d) (decodeBase ix) (decodeBase iy) := by
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
  constructor
  · exact (wide_add_success h0 we14 out (scale we2 h0 quarter Hh0).1
      (SAQ_RawWide.mul_exact alpha we13 we14 Hwe14).1 run).1
  · have e := SAQ_RawWide.add_exact h0 we14 out run
    rw [(SAQ_RawWide.mul_exact alpha we13 we14 Hwe14).2,
      SAQ_RawWide.add_exact h1 we12 we13 Hwe13,
      (SAQ_RawWide.mul_exact alpha we11 we12 Hwe12).2,
      SAQ_RawWide.add_exact h2 we10 we11 Hwe11,
      (SAQ_RawWide.mul_exact alpha h3 we10 Hwe10).2,
      (scale we9 h3 m2 Hh3).2,
      (baseMul m1 iy m2 Hm2).2,
      SAQ_RawWide.sub_exact we8 d we9 Hwe9,
      SAQ_RawWide.add_exact we3 c we8 Hwe8,
      (scale we7 h2 m1 Hh2).2,
      (baseMul SAQ_LineSource.quarter ix m1 Hm1).2,
      SAQ_RawWide.sub_exact we6 d we7 Hwe7,
      SAQ_RawWide.sub_exact we c we6 Hwe6,
      (scale we5 h1 m Hh1).2,
      (baseMul SAQ_LineSource.quarter iy m Hm).2,
      SAQ_RawWide.add_exact we4 d we5 Hwe5,
      SAQ_RawWide.sub_exact we3 c we4 Hwe4,
      SAQ_RawWide.sub_exact a b we3 Hwe3,
      (scale we2 h0 SAQ_LineSource.quarter Hh0).2,
      SAQ_RawWide.add_exact we1 d we2 Hwe2,
      SAQ_RawWide.add_exact we c we1 Hwe1,
      SAQ_RawWide.add_exact a b we Hwe] at e
    exact e

#print axioms made
end AspisR1.FIp_CircleValue
end
