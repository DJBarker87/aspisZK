import QueriedInverse
import SharedInverseReplay

/-! Constructed ordered line/norm buffers and shared inversion input. The
point type carries its circle invariant; neither norms, line coordinates,
denominator values nor reciprocals are caller-supplied hints. This is the
source-shaped field/list algorithm, not a mutable Rust Vec translation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 30000
namespace AspisV8.LineNormBuffer
noncomputable section
open AspisV5ComponentCQM31TowerExact
open AspisV8.QueriedInverse
abbrev Point := CircleNorm.UnitPoint M31Exact

local instance twoC : NeZero (2 : C) := ⟨by
  intro h
  have hh := congrArg QuadraticAlgebra.re h
  have hm : (2 : M31Exact)=0 := by
    simpa only [QuadraticAlgebra.re_ofNat,QuadraticAlgebra.re_zero] using hh
  exact (by decide : (2 : M31Exact)≠0) hm⟩

/-- Literal canonical low31 half, on each CM31 coordinate. -/
def halfC (n : C) : C :=
  ⟨(LineNorm.halfWord n.re.val : M31Exact),(LineNorm.halfWord n.im.val : M31Exact)⟩

theorem halfC_double (n : C) : 2*halfC n=n := by
  have hr := LineNorm.half_cast n.re.val (ZMod.val_lt n.re)
  have hi := LineNorm.half_cast n.im.val (ZMod.val_lt n.im)
  change 2*(LineNorm.halfWord n.re.val : M31Exact)=(n.re.val : M31Exact) at hr
  change 2*(LineNorm.halfWord n.im.val : M31Exact)=(n.im.val : M31Exact) at hi
  simp only [ZMod.natCast_zmod_val] at hr hi
  ext
  · simpa only [halfC,QuadraticAlgebra.re_mul,QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat,zero_mul,mul_zero,add_zero] using hr
  · simpa only [halfC,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat,zero_mul,mul_zero,add_zero] using hi

theorem halfC_eq (n : C) : halfC n=n/2 := by
  apply (eq_div_iff (NeZero.ne (2 : C))).mpr
  simpa only [mul_comm] using halfC_double n

def polar (v w : K) : C := 2*(v.re*w.re-qm31R*v.im*w.im)

def prepare (a b c : K) : Fin 5 → C :=
  let nc := normK c
  let half := halfC (normK b-nc)
  ![normK a+nc+half,half,polar a b,polar a c,polar b c]

def fourList {F : Type*} (v : F × F × F × F) : List F := [v.1,v.2.1,v.2.2.1,v.2.2.2]

def normFour (coeff : Fin 5 → C) (x y t : M31Exact) : List C :=
  fourList (LineNorm.four
    (coeff 0+coeff 1*algebraMap M31Exact C t)
    (coeff 2*algebraMap M31Exact C x)
    (coeff 3*algebraMap M31Exact C y)
    (coeff 4*algebraMap M31Exact C (x*y)))

def scale (v : K) (x : M31Exact) : K :=
  ⟨v.re*algebraMap M31Exact C x,v.im*algebraMap M31Exact C x⟩

def pointValues (a b c : K) (p : Point) : List K :=
  let bx := scale b p.val.1
  let cy := scale c p.val.2
  [a+bx+cy,a+bx-cy,a-bx-cy,a-bx+cy]

theorem map_line (x : M31Exact) :
    algebraMap M31Exact C (LineNorm.line x)=LineNorm.line (algebraMap M31Exact C x) := by
  simp only [LineNorm.line,map_sub,map_mul,map_pow,map_ofNat,map_one]

theorem point_norms (a b c : K) (p : Point) :
    normFour (prepare a b c) p.val.1 p.val.2 (LineNorm.line p.val.1)=
      (pointValues a b c p).map normK := by
  have circle := CircleNorm.map_unit (algebraMap M31Exact C) p.val.1 p.val.2 p.property
  have h := QueriedInverse.lineFour_norms qm31R a.re a.im b.re b.im c.re c.im
    (algebraMap M31Exact C p.val.1) (algebraMap M31Exact C p.val.2) circle
  have mapped := congrArg fourList h
  simpa only [normFour,prepare,halfC_eq,map_line,map_mul,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,QueriedInverse.lineFour,LineNorm.four,fourList,
    Matrix.head_cons,Matrix.tail_cons,
    pointValues,List.map_cons,List.map_nil,normK,scale,polar,
    ChordNorm.norm,ChordNorm.polar,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub] using mapped

/-- The same traversal constructs t and then zips points with that derived
buffer. No equality with an independently supplied coordinate list is used. -/
def lines (points : List Point) : List M31Exact := points.map fun p=>LineNorm.line p.val.1
def values (a b c : K) (points : List Point) : List K := points.flatMap (pointValues a b c)
def norms (a b c : K) (points : List Point) : List C :=
  (points.zip (lines points)).flatMap fun pt=>
    normFour (prepare a b c) pt.1.val.1 pt.1.val.2 pt.2
def base (points : List Point) : List M31Exact :=
  points.flatMap fun p=>[2*p.val.1,2*p.val.2]

theorem norms_eq (a b c : K) (points : List Point) :
    norms a b c points=(values a b c points).map normK := by
  induction points with
  | nil => rfl
  | cons p points ih =>
    simp only [norms,lines,List.map_cons,List.zip_cons_cons,List.flatMap_cons,
      values,List.map_append] at ih ⊢
    rw [point_norms]
    exact congrArg (fun rest=>(List.map normK (pointValues a b c p))++rest) ih

theorem scalar_norms_eq (a b c : K) (points : List Point) :
    (norms a b c points).map normC=(values a b c points).map scalarNorm := by
  rw [norms_eq,List.map_map]
  rfl

theorem buffer_lengths (a b c : K) (points : List Point) :
    (values a b c points).length=4*points.length ∧
    (norms a b c points).length=4*points.length ∧
    (base points).length=2*points.length ∧ (lines points).length=points.length := by
  have hv : (values a b c points).length=4*points.length := by
    induction points with
    | nil => rfl
    | cons p points ih => simp [values,pointValues] at ih ⊢; omega
  have hb : (base points).length=2*points.length := by
    induction points with
    | nil => rfl
    | cons p points ih => simp [base] at ih ⊢; omega
  exact ⟨hv,by rw [norms_eq,List.length_map,hv],hb,by simp [lines]⟩

def rebuildWith (v : K) (n : C) (d : M) : K :=
  let ni : C := ⟨n.re*d,-n.im*d⟩
  ⟨v.re*ni,-v.im*ni⟩

theorem zip_rebuildWith (vs : List K) (ds : List M) :
    List.zipWith (fun vn d=>rebuildWith vn.1 vn.2 d)
      (vs.zip (vs.map normK)) ds = List.zipWith rebuild vs ds := by
  induction vs generalizing ds with
  | nil => simp
  | cons v vs ih =>
    cases ds with
    | nil => simp
    | cons d ds =>
      simp only [List.map_cons,List.zip_cons_cons,List.zipWith_cons_cons,ih]
      rfl

/-- Modeled line_norm::inverse inputs are fully derived from points/chord;
both CM31 norms and inverse seeds are actually consumed by reconstruction. -/
def inverseLines (a b c : K) (points : List Point) : Option (List K × List M) :=
  let vs := values a b c points
  if vs=[] ∨ (0 : K)∈vs then none else do
    let ns := norms a b c points
    let (inverse,baseInverse) ← SharedInverseReplay.batchTwo (ns.map normC) (base points)
    pure (List.zipWith (fun vn d=>rebuildWith vn.1 vn.2 d) (vs.zip ns) inverse,baseInverse)

theorem inverseLines_eq_checked (a b c : K) (points : List Point) :
    inverseLines a b c points=QueriedInverse.checked (values a b c points) (base points) := by
  dsimp only [inverseLines,QueriedInverse.checked]
  rw [scalar_norms_eq,SharedInverseReplay.batchTwo_eq_separate,norms_eq]
  simp only [zip_rebuildWith]

#print axioms halfC_double
#print axioms halfC_eq
#print axioms point_norms
#print axioms norms_eq
#print axioms scalar_norms_eq
#print axioms buffer_lengths
#print axioms inverseLines_eq_checked
end
end AspisV8.LineNormBuffer
