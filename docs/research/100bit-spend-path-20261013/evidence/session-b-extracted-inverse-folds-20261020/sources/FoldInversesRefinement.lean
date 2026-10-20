import FoldInversesExplicitOps
import R1ZCircleFoldMathV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FoldInverses.Refinement
abbrev E := aspis_core.field.WideExact
abbrev B := aspis_core.field.M31
abbrev P := AspisCircleGroupOrder.P
def CanonicalBase (x : B) : Prop := x.val < P
def decodeBase (x : B) : ZMod P := (x.val : ZMod P)
def values4 {K : Type} (a b c d : K) (i : Fin 4) : K :=
  match i.val with | 0 => a | 1 => b | 2 => c | _ => d

private theorem values4_0 {K : Type} (a b c d : K) : values4 a b c d 0 = a := rfl
private theorem values4_1 {K : Type} (a b c d : K) : values4 a b c d 1 = b := rfl
private theorem values4_2 {K : Type} (a b c d : K) : values4 a b c d 2 = c := rfl
private theorem values4_3 {K : Type} (a b c d : K) : values4 a b c d 3 = d := rfl

structure OperationsRefine {K : Type} [Field K] [Algebra (ZMod P) K]
    (ops : FoldOps) (canonical : E → Prop) (decode : E → K) : Prop where
  add : ∀ x y z, canonical x → canonical y → ops.add x y = .ok z →
    canonical z ∧ decode z = decode x + decode y
  sub : ∀ x y z, canonical x → canonical y → ops.sub x y = .ok z →
    canonical z ∧ decode z = decode x - decode y
  mul : ∀ x y z, canonical x → canonical y → ops.mul x y = .ok z →
    canonical z ∧ decode z = decode x * decode y
  scale : ∀ x y z, canonical x → CanonicalBase y → ops.scale x y = .ok z →
    canonical z ∧ decode z = decode x * algebraMap (ZMod P) K (decodeBase y)
  baseMul : ∀ x y z, CanonicalBase x → CanonicalBase y → ops.baseMul x y = .ok z →
    CanonicalBase z ∧ decodeBase z = decodeBase x * decodeBase y

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem canonicalQuarter : CanonicalBase weights.QUARTER := by
  unfold CanonicalBase weights.QUARTER
  change (536870912 : Nat) < 2147483647
  decide
private theorem canonicalHalf : CanonicalBase (1073741824#u32) := by
  unfold CanonicalBase
  change (1073741824 : Nat) < 2147483647
  decide
private theorem decodeQuarter : decodeBase weights.QUARTER = R1ZCircleFoldMathV1.rustQuarter := by
  unfold decodeBase weights.QUARTER R1ZCircleFoldMathV1.rustQuarter
  rfl
private theorem decodeHalf : decodeBase (1073741824#u32) = R1ZCircleFoldMathV1.rustHalf := rfl

variable {K : Type} [Field K] [Algebra (ZMod P) K]

theorem circle_success (ops : FoldOps) (canonical : E → Prop) (decode : E → K)
    (R : OperationsRefine ops canonical decode) (alpha a b c d out : E)
    (ix iy lx ly lz : B)
    (Ca : canonical a) (Cb : canonical b) (Cc : canonical c) (Cd : canonical d)
    (Calpha : canonical alpha)
    (Cix : CanonicalBase ix) (Ciy : CanonicalBase iy)
    (h : verifier.circle_fold_with_inverses ops alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz]) = .ok out) :
    canonical out ∧ decode out = R1ZCircleFoldMathV1.sourceCircleFold (decode alpha) (values4 (decode a) (decode b) (decode c) (decode d)) (decodeBase ix) (decodeBase iy) := by
  have ia0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
  have ia1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
  have ia2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
  have ia3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl
  have ii0 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 0#usize = .ok ix := rfl
  have ii1 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 1#usize = .ok iy := rfl
  simp only [verifier.circle_fold_with_inverses, ia0, ia1, ia2, ia3, ii0, ii1, bind_tc_ok] at h
  obtain ⟨we,Hwe,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe,Ewe⟩ := R.add a b we Ca Cb Hwe
  obtain ⟨we1,Hwe1,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe1,Ewe1⟩ := R.add we c we1 Cwe Cc Hwe1
  obtain ⟨we2,Hwe2,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe2,Ewe2⟩ := R.add we1 d we2 Cwe1 Cd Hwe2
  obtain ⟨h0,Hh0,h⟩ := bind_success _ _ _ h
  obtain ⟨Ch0,Eh0⟩ := R.scale we2 weights.QUARTER h0 Cwe2 canonicalQuarter Hh0
  obtain ⟨we3,Hwe3,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe3,Ewe3⟩ := R.sub a b we3 Ca Cb Hwe3
  obtain ⟨we4,Hwe4,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe4,Ewe4⟩ := R.sub we3 c we4 Cwe3 Cc Hwe4
  obtain ⟨we5,Hwe5,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe5,Ewe5⟩ := R.add we4 d we5 Cwe4 Cd Hwe5
  obtain ⟨m,Hm,h⟩ := bind_success _ _ _ h
  obtain ⟨Cm,Em⟩ := R.baseMul weights.QUARTER iy m canonicalQuarter Ciy Hm
  obtain ⟨h1,Hh1,h⟩ := bind_success _ _ _ h
  obtain ⟨Ch1,Eh1⟩ := R.scale we5 m h1 Cwe5 Cm Hh1
  obtain ⟨we6,Hwe6,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe6,Ewe6⟩ := R.sub we c we6 Cwe Cc Hwe6
  obtain ⟨we7,Hwe7,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe7,Ewe7⟩ := R.sub we6 d we7 Cwe6 Cd Hwe7
  obtain ⟨m1,Hm1,h⟩ := bind_success _ _ _ h
  obtain ⟨Cm1,Em1⟩ := R.baseMul weights.QUARTER ix m1 canonicalQuarter Cix Hm1
  obtain ⟨h2,Hh2,h⟩ := bind_success _ _ _ h
  obtain ⟨Ch2,Eh2⟩ := R.scale we7 m1 h2 Cwe7 Cm1 Hh2
  obtain ⟨we8,Hwe8,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe8,Ewe8⟩ := R.add we3 c we8 Cwe3 Cc Hwe8
  obtain ⟨we9,Hwe9,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe9,Ewe9⟩ := R.sub we8 d we9 Cwe8 Cd Hwe9
  obtain ⟨m2,Hm2,h⟩ := bind_success _ _ _ h
  obtain ⟨Cm2,Em2⟩ := R.baseMul m1 iy m2 Cm1 Ciy Hm2
  obtain ⟨h3,Hh3,h⟩ := bind_success _ _ _ h
  obtain ⟨Ch3,Eh3⟩ := R.scale we9 m2 h3 Cwe9 Cm2 Hh3
  obtain ⟨we10,Hwe10,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe10,Ewe10⟩ := R.mul alpha h3 we10 Calpha Ch3 Hwe10
  obtain ⟨we11,Hwe11,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe11,Ewe11⟩ := R.add h2 we10 we11 Ch2 Cwe10 Hwe11
  obtain ⟨we12,Hwe12,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe12,Ewe12⟩ := R.mul alpha we11 we12 Calpha Cwe11 Hwe12
  obtain ⟨we13,Hwe13,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe13,Ewe13⟩ := R.add h1 we12 we13 Ch1 Cwe12 Hwe13
  obtain ⟨we14,Hwe14,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe14,Ewe14⟩ := R.mul alpha we13 we14 Calpha Cwe13 Hwe14
  obtain ⟨Cout,Eout⟩ := R.add h0 we14 out Ch0 Cwe14 h
  refine ⟨Cout,?_⟩
  simpa only [R1ZCircleFoldMathV1.sourceCircleFold, values4_0, values4_1, values4_2, values4_3, decodeQuarter, decodeHalf, Ewe14, Ewe13, Ewe12, Ewe11, Ewe10, Eh3, Em2, Ewe9, Ewe8, Eh2, Em1, Ewe7, Ewe6, Eh1, Em, Ewe5, Ewe4, Ewe3, Eh0, Ewe2, Ewe1, Ewe] using Eout
#print axioms circle_success

theorem line_success (ops : FoldOps) (canonical : E → Prop) (decode : E → K)
    (R : OperationsRefine ops canonical decode) (alpha a b c d out : E)
    (ix iy lx ly lz : B)
    (Ca : canonical a) (Cb : canonical b) (Cc : canonical c) (Cd : canonical d)
    (Calpha : canonical alpha)
    (Clx : CanonicalBase lx) (Cly : CanonicalBase ly) (Clz : CanonicalBase lz)
    (h : verifier.line_fold_with_inverses ops alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz]) = .ok out) :
    canonical out ∧ decode out = R1ZCircleFoldMathV1.sourceLineFold (decode alpha) (values4 (decode a) (decode b) (decode c) (decode d)) (decodeBase lx) (decodeBase ly) (decodeBase lz) := by
  have ia0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
  have ia1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
  have ia2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
  have ia3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl
  have ii2 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 2#usize = .ok lx := rfl
  have ii3 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 3#usize = .ok ly := rfl
  have ii4 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 4#usize = .ok lz := rfl
  simp only [verifier.line_fold_with_inverses, ia0, ia1, ia2, ia3, ii2, ii3, ii4, bind_tc_ok] at h
  obtain ⟨we,Hwe,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe,Ewe⟩ := R.add a b we Ca Cb Hwe
  obtain ⟨we1,Hwe1,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe1,Ewe1⟩ := R.add we c we1 Cwe Cc Hwe1
  obtain ⟨we2,Hwe2,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe2,Ewe2⟩ := R.add we1 d we2 Cwe1 Cd Hwe2
  obtain ⟨h0,Hh0,h⟩ := bind_success _ _ _ h
  obtain ⟨Ch0,Eh0⟩ := R.scale we2 weights.QUARTER h0 Cwe2 canonicalQuarter Hh0
  obtain ⟨we3,Hwe3,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe3,Ewe3⟩ := R.sub we c we3 Cwe Cc Hwe3
  obtain ⟨we4,Hwe4,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe4,Ewe4⟩ := R.sub we3 d we4 Cwe3 Cd Hwe4
  obtain ⟨m,Hm,h⟩ := bind_success _ _ _ h
  obtain ⟨Cm,Em⟩ := R.baseMul weights.QUARTER lz m canonicalQuarter Clz Hm
  obtain ⟨h2,Hh2,h⟩ := bind_success _ _ _ h
  obtain ⟨Ch2,Eh2⟩ := R.scale we4 m h2 Cwe4 Cm Hh2
  obtain ⟨we5,Hwe5,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe5,Ewe5⟩ := R.sub a b we5 Ca Cb Hwe5
  obtain ⟨m1,Hm1,h⟩ := bind_success _ _ _ h
  obtain ⟨Cm1,Em1⟩ := R.baseMul 1073741824#u32 lx m1 canonicalHalf Clx Hm1
  obtain ⟨c0,Hc0,h⟩ := bind_success _ _ _ h
  obtain ⟨Cc0,Ec0⟩ := R.scale we5 m1 c0 Cwe5 Cm1 Hc0
  obtain ⟨we6,Hwe6,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe6,Ewe6⟩ := R.sub d c we6 Cd Cc Hwe6
  obtain ⟨m2,Hm2,h⟩ := bind_success _ _ _ h
  obtain ⟨Cm2,Em2⟩ := R.baseMul 1073741824#u32 ly m2 canonicalHalf Cly Hm2
  obtain ⟨c1,Hc1,h⟩ := bind_success _ _ _ h
  obtain ⟨Cc1,Ec1⟩ := R.scale we6 m2 c1 Cwe6 Cm2 Hc1
  obtain ⟨we7,Hwe7,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe7,Ewe7⟩ := R.add c0 c1 we7 Cc0 Cc1 Hwe7
  obtain ⟨h1,Hh1,h⟩ := bind_success _ _ _ h
  obtain ⟨Ch1,Eh1⟩ := R.scale we7 1073741824#u32 h1 Cwe7 canonicalHalf Hh1
  obtain ⟨we8,Hwe8,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe8,Ewe8⟩ := R.sub c0 c1 we8 Cc0 Cc1 Hwe8
  obtain ⟨m3,Hm3,h⟩ := bind_success _ _ _ h
  obtain ⟨Cm3,Em3⟩ := R.baseMul 1073741824#u32 lz m3 canonicalHalf Clz Hm3
  obtain ⟨h3,Hh3,h⟩ := bind_success _ _ _ h
  obtain ⟨Ch3,Eh3⟩ := R.scale we8 m3 h3 Cwe8 Cm3 Hh3
  obtain ⟨we9,Hwe9,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe9,Ewe9⟩ := R.mul alpha h3 we9 Calpha Ch3 Hwe9
  obtain ⟨we10,Hwe10,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe10,Ewe10⟩ := R.add h2 we9 we10 Ch2 Cwe9 Hwe10
  obtain ⟨we11,Hwe11,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe11,Ewe11⟩ := R.mul alpha we10 we11 Calpha Cwe10 Hwe11
  obtain ⟨we12,Hwe12,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe12,Ewe12⟩ := R.add h1 we11 we12 Ch1 Cwe11 Hwe12
  obtain ⟨we13,Hwe13,h⟩ := bind_success _ _ _ h
  obtain ⟨Cwe13,Ewe13⟩ := R.mul alpha we12 we13 Calpha Cwe12 Hwe13
  obtain ⟨Cout,Eout⟩ := R.add h0 we13 out Ch0 Cwe13 h
  refine ⟨Cout,?_⟩
  simpa only [R1ZCircleFoldMathV1.sourceLineFold, values4_0, values4_1, values4_2, values4_3, decodeQuarter, decodeHalf, Ewe13, Ewe12, Ewe11, Ewe10, Ewe9, Eh3, Em3, Ewe8, Eh1, Ewe7, Ec1, Em2, Ewe6, Ec0, Em1, Ewe5, Eh2, Em, Ewe4, Ewe3, Eh0, Ewe2, Ewe1, Ewe] using Eout
#print axioms line_success
end AspisR1FoldInverses.Refinement
