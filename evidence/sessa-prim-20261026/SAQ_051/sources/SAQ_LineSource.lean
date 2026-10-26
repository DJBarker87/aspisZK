import SAQ_RawWide
import SAQ_LineEmbedding
import R1ZCircleFoldMathV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_LineSource
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof
abbrev FP := ZMod AspisCircleGroupOrder.P
def quarter : U32 := 536870912#u32
def values4 {K : Type} (a b c d : K) (i : Fin 4) : K :=
  match i.val with | 0 => a | 1 => b | 2 => c | _ => d
private theorem values4_0 {K : Type} (a b c d : K) : values4 a b c d 0=a := rfl
private theorem values4_1 {K : Type} (a b c d : K) : values4 a b c d 1=b := rfl
private theorem values4_2 {K : Type} (a b c d : K) : values4 a b c d 2=c := rfl
private theorem values4_3 {K : Type} (a b c d : K) : values4 a b c d 3=d := rfl
private theorem decodeQuarter : SAQ_LineEmbedding.decode quarter=R1ZCircleFoldMathV1.rustQuarter := rfl
private theorem decodeHalf : SAQ_LineEmbedding.decode (1073741824#u32)=R1ZCircleFoldMathV1.rustHalf := rfl

theorem baseMul (x y z : U32) (h : field.M31.mul x y=ok z) :
    z.val<2147483647 ∧ SAQ_LineEmbedding.decode z=SAQ_LineEmbedding.decode x*SAQ_LineEmbedding.decode y := by
  rw [m31_mul_same] at h
  exact ⟨R17CurrentDomainCanonical.mul_success_canonical x y z h,
    R17CurrentM31Semantics.current_mul_decode x y z h⟩

def line
  (alpha : E)
  (a : Array E 4#usize)
  (inverse : Array U32 5#usize) :
  Result E
  := do
  let ix ← Array.index_usize inverse 2#usize
  let iy ← Array.index_usize inverse 3#usize
  let iz ← Array.index_usize inverse 4#usize
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let we ← field.wide_exact.WideExact.add a1 b
  let we1 ← field.wide_exact.WideExact.add we c
  let we2 ← field.wide_exact.WideExact.add we1 d
  let h0 ← field.wide_exact.WideExact.mul_m31 we2 quarter
  let we3 ← field.wide_exact.WideExact.sub we c
  let we4 ← field.wide_exact.WideExact.sub we3 d
  let m ← field.M31.mul quarter iz
  let h2 ← field.wide_exact.WideExact.mul_m31 we4 m
  let we5 ← field.wide_exact.WideExact.sub a1 b
  let m1 ← field.M31.mul 1073741824#u32 ix
  let c0 ← field.wide_exact.WideExact.mul_m31 we5 m1
  let we6 ← field.wide_exact.WideExact.sub d c
  let m2 ← field.M31.mul 1073741824#u32 iy
  let c1 ← field.wide_exact.WideExact.mul_m31 we6 m2
  let we7 ← field.wide_exact.WideExact.add c0 c1
  let h1 ← field.wide_exact.WideExact.mul_m31 we7 1073741824#u32
  let we8 ← field.wide_exact.WideExact.sub c0 c1
  let m3 ← field.M31.mul 1073741824#u32 iz
  let h3 ← field.wide_exact.WideExact.mul_m31 we8 m3
  let we9 ← field.wide_exact.WideExact.mul alpha h3
  let we10 ← field.wide_exact.WideExact.add h2 we9
  let we11 ← field.wide_exact.WideExact.mul alpha we10
  let we12 ← field.wide_exact.WideExact.add h1 we11
  let we13 ← field.wide_exact.WideExact.mul alpha we12
  field.wide_exact.WideExact.add h0 we13

theorem line_made_exact (alpha a b c d out : E)
    (ix iy lx ly lz : U32)
    (h : line alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz]) = .ok out) :
    CanonicalWide out ∧ decodeWide out = R1ZCircleFoldMathV1.sourceLineFold (decodeWide alpha) (values4 (decodeWide a) (decodeWide b) (decodeWide c) (decodeWide d)) (SAQ_LineEmbedding.decode lx) (SAQ_LineEmbedding.decode ly) (SAQ_LineEmbedding.decode lz) := by
  have ia0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
  have ia1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
  have ia2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
  have ia3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl
  have ii2 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 2#usize = .ok lx := rfl
  have ii3 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 3#usize = .ok ly := rfl
  have ii4 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 4#usize = .ok lz := rfl
  simp only [line, ia0, ia1, ia2, ia3, ii2, ii3, ii4, bind_tc_ok] at h
  obtain ⟨we,Hwe,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe := SAQ_RawWide.add_exact a b we Hwe
  obtain ⟨we1,Hwe1,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe1 := SAQ_RawWide.add_exact we c we1 Hwe1
  obtain ⟨we2,Hwe2,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe2 := SAQ_RawWide.add_exact we1 d we2 Hwe2
  obtain ⟨h0,Hh0,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Ch0,Eh0⟩ := SAQ_LineEmbedding.scale we2 h0 quarter Hh0
  obtain ⟨we3,Hwe3,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe3 := SAQ_RawWide.sub_exact we c we3 Hwe3
  obtain ⟨we4,Hwe4,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe4 := SAQ_RawWide.sub_exact we3 d we4 Hwe4
  obtain ⟨m,Hm,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Cm,Em⟩ := baseMul quarter lz m Hm
  obtain ⟨h2,Hh2,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Ch2,Eh2⟩ := SAQ_LineEmbedding.scale we4 h2 m Hh2
  obtain ⟨we5,Hwe5,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe5 := SAQ_RawWide.sub_exact a b we5 Hwe5
  obtain ⟨m1,Hm1,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Cm1,Em1⟩ := baseMul 1073741824#u32 lx m1 Hm1
  obtain ⟨c0,Hc0,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Cc0,Ec0⟩ := SAQ_LineEmbedding.scale we5 c0 m1 Hc0
  obtain ⟨we6,Hwe6,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe6 := SAQ_RawWide.sub_exact d c we6 Hwe6
  obtain ⟨m2,Hm2,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Cm2,Em2⟩ := baseMul 1073741824#u32 ly m2 Hm2
  obtain ⟨c1,Hc1,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Cc1,Ec1⟩ := SAQ_LineEmbedding.scale we6 c1 m2 Hc1
  obtain ⟨we7,Hwe7,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe7 := SAQ_RawWide.add_exact c0 c1 we7 Hwe7
  obtain ⟨h1,Hh1,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Ch1,Eh1⟩ := SAQ_LineEmbedding.scale we7 h1 1073741824#u32 Hh1
  obtain ⟨we8,Hwe8,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe8 := SAQ_RawWide.sub_exact c0 c1 we8 Hwe8
  obtain ⟨m3,Hm3,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Cm3,Em3⟩ := baseMul 1073741824#u32 lz m3 Hm3
  obtain ⟨h3,Hh3,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Ch3,Eh3⟩ := SAQ_LineEmbedding.scale we8 h3 m3 Hh3
  obtain ⟨we9,Hwe9,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Cwe9,Ewe9⟩ := SAQ_RawWide.mul_exact alpha h3 we9 Hwe9
  obtain ⟨we10,Hwe10,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe10 := SAQ_RawWide.add_exact h2 we9 we10 Hwe10
  obtain ⟨we11,Hwe11,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Cwe11,Ewe11⟩ := SAQ_RawWide.mul_exact alpha we10 we11 Hwe11
  obtain ⟨we12,Hwe12,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have Ewe12 := SAQ_RawWide.add_exact h1 we11 we12 Hwe12
  obtain ⟨we13,Hwe13,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨Cwe13,Ewe13⟩ := SAQ_RawWide.mul_exact alpha we12 we13 Hwe13
  obtain ⟨Cout,Eout⟩ := wide_add_success h0 we13 out Ch0 Cwe13 h
  refine ⟨Cout,?_⟩
  rw [Ewe2,Ewe1,Ewe] at Eh0
  rw [Em,Ewe4,Ewe3,Ewe] at Eh2
  rw [Em1,Ewe5] at Ec0
  rw [Em2,Ewe6] at Ec1
  rw [Ewe7,Ec0,Ec1] at Eh1
  rw [Em3,Ewe8,Ec0,Ec1] at Eh3
  rw [Ewe13,Ewe12,Ewe11,Ewe10,Ewe9] at Eout
  rw [Eh0,Eh1,Eh2,Eh3] at Eout
  simpa only [R1ZCircleFoldMathV1.sourceLineFold,values4_0,values4_1,values4_2,
    values4_3,decodeQuarter,decodeHalf] using Eout

#print axioms baseMul
#print axioms line_made_exact
end AspisR1.SAQ_LineSource
end
