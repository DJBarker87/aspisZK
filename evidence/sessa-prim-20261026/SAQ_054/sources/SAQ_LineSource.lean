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
def decodeBase (x : U32) : FP := x.val
def values4 {K : Type} (a b c d : K) (i : Fin 4) : K :=
  match i.val with | 0 => a | 1 => b | 2 => c | _ => d
private theorem values4_0 {K : Type} (a b c d : K) : values4 a b c d 0=a := rfl
private theorem values4_1 {K : Type} (a b c d : K) : values4 a b c d 1=b := rfl
private theorem values4_2 {K : Type} (a b c d : K) : values4 a b c d 2=c := rfl
private theorem values4_3 {K : Type} (a b c d : K) : values4 a b c d 3=d := rfl
private theorem decodeQuarter : decodeBase quarter=R1ZCircleFoldMathV1.rustQuarter := rfl
private theorem decodeHalf : decodeBase (1073741824#u32)=R1ZCircleFoldMathV1.rustHalf := rfl

theorem baseMul (x y z : U32) (h : field.M31.mul x y=ok z) :
    z.val<2147483647 ∧ decodeBase z=decodeBase x*decodeBase y := by
  rw [m31_mul_same] at h
  exact ⟨R17CurrentDomainCanonical.mul_success_canonical x y z h,
    R17CurrentM31Semantics.current_mul_decode x y z h⟩

theorem scale (x z : E) (s : U32) (h : field.wide_exact.WideExact.mul_m31 x s=ok z) :
    CanonicalWide z ∧ decodeWide z=decodeWide x *
      algebraMap FP AspisWideTower.WideExact (decodeBase s) :=
  SAQ_LineEmbedding.scale x z s h

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

structure Cuts (alpha a b c d : E) (lx ly lz : U32) (out : E) where
  we : E
  we1 : E
  we2 : E
  h0 : E
  we3 : E
  we4 : E
  m : U32
  h2 : E
  we5 : E
  m1 : U32
  c0 : E
  we6 : E
  m2 : U32
  c1 : E
  we7 : E
  h1 : E
  we8 : E
  m3 : U32
  h3 : E
  we9 : E
  we10 : E
  we11 : E
  we12 : E
  we13 : E
  Hwe : field.wide_exact.WideExact.add a b=ok we
  Hwe1 : field.wide_exact.WideExact.add we c=ok we1
  Hwe2 : field.wide_exact.WideExact.add we1 d=ok we2
  Hh0 : field.wide_exact.WideExact.mul_m31 we2 quarter=ok h0
  Hwe3 : field.wide_exact.WideExact.sub we c=ok we3
  Hwe4 : field.wide_exact.WideExact.sub we3 d=ok we4
  Hm : field.M31.mul quarter lz=ok m
  Hh2 : field.wide_exact.WideExact.mul_m31 we4 m=ok h2
  Hwe5 : field.wide_exact.WideExact.sub a b=ok we5
  Hm1 : field.M31.mul 1073741824#u32 lx=ok m1
  Hc0 : field.wide_exact.WideExact.mul_m31 we5 m1=ok c0
  Hwe6 : field.wide_exact.WideExact.sub d c=ok we6
  Hm2 : field.M31.mul 1073741824#u32 ly=ok m2
  Hc1 : field.wide_exact.WideExact.mul_m31 we6 m2=ok c1
  Hwe7 : field.wide_exact.WideExact.add c0 c1=ok we7
  Hh1 : field.wide_exact.WideExact.mul_m31 we7 1073741824#u32=ok h1
  Hwe8 : field.wide_exact.WideExact.sub c0 c1=ok we8
  Hm3 : field.M31.mul 1073741824#u32 lz=ok m3
  Hh3 : field.wide_exact.WideExact.mul_m31 we8 m3=ok h3
  Hwe9 : field.wide_exact.WideExact.mul alpha h3=ok we9
  Hwe10 : field.wide_exact.WideExact.add h2 we9=ok we10
  Hwe11 : field.wide_exact.WideExact.mul alpha we10=ok we11
  Hwe12 : field.wide_exact.WideExact.add h1 we11=ok we12
  Hwe13 : field.wide_exact.WideExact.mul alpha we12=ok we13
  Hout : field.wide_exact.WideExact.add h0 we13=ok out

theorem cuts (alpha a b c d out : E) (ix iy lx ly lz : U32)
    (h : line alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out) :
    Nonempty (Cuts alpha a b c d lx ly lz out) := by
  have ia0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
  have ia1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
  have ia2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
  have ia3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl
  have ii2 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 2#usize = .ok lx := rfl
  have ii3 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 3#usize = .ok ly := rfl
  have ii4 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 4#usize = .ok lz := rfl
  simp only [line, ia0, ia1, ia2, ia3, ii2, ii3, ii4, bind_tc_ok] at h
  obtain ⟨we,Hwe,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we1,Hwe1,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we2,Hwe2,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨h0,Hh0,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we3,Hwe3,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we4,Hwe4,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨m,Hm,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨h2,Hh2,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we5,Hwe5,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨m1,Hm1,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨c0,Hc0,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we6,Hwe6,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨m2,Hm2,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨c1,Hc1,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we7,Hwe7,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨h1,Hh1,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we8,Hwe8,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨m3,Hm3,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨h3,Hh3,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we9,Hwe9,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we10,Hwe10,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we11,Hwe11,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we12,Hwe12,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨we13,Hwe13,h⟩ := Port3_PushFrame.bind_success _ _ _ h
  exact ⟨⟨we,we1,we2,h0,we3,we4,m,h2,we5,m1,c0,we6,m2,c1,we7,h1,we8,m3,h3,we9,we10,we11,we12,we13,Hwe,Hwe1,Hwe2,Hh0,Hwe3,Hwe4,Hm,Hh2,Hwe5,Hm1,Hc0,Hwe6,Hm2,Hc1,Hwe7,Hh1,Hwe8,Hm3,Hh3,Hwe9,Hwe10,Hwe11,Hwe12,Hwe13,h⟩⟩

#print axioms cuts
end AspisR1.SAQ_LineSource
end
