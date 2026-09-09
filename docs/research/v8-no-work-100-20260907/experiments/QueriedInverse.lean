import JoinedInverse
import CircleNorm
import LineNorm
import AspisFormal.V5ComponentCQM31TowerExact

/-! Field-level model of the retained nested-norm inversion. The source
canonical parser, selected point lookup and mutable Vec loops are not translated
by this leaf. No successful-inverse or norm-equality premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 30000
namespace AspisV8.QueriedInverse
noncomputable section
open AspisV5ComponentCQM31TowerExact
abbrev K := QM31Exact
abbrev M := M31Exact
abbrev C := CM31Exact

def normK (v : K) : C := v.re^2-qm31R*v.im^2
def normC (n : C) : M := n.re^2+n.im^2
def scalarNorm (v : K) : M := normC (normK v)

theorem normK_eq (v : K) : normK v=QuadraticAlgebra.norm v := by
  simp only [normK,QuadraticAlgebra.norm_def,zero_mul]
  ring
theorem normC_eq (v : C) : normC v=QuadraticAlgebra.norm v := by
  simp only [normC,QuadraticAlgebra.norm_def,zero_mul]
  ring
theorem scalarNorm_zero_iff (v : K) : scalarNorm v=0 ↔ v=0 := by
  rw [scalarNorm,normC_eq,QuadraticAlgebra.norm_eq_zero_iff_eq_zero,
    normK_eq,QuadraticAlgebra.norm_eq_zero_iff_eq_zero]

/-- Literal source reconstruction from one base-field reciprocal: first
conjugate/divide CM31 norm, then conjugate/divide QM31 value. -/
def rebuild (v : K) (d : M) : K :=
  let n := normK v
  let ni : C := ⟨n.re*d,-n.im*d⟩
  ⟨v.re*ni,-v.im*ni⟩

theorem rebuild_correct (v : K) : rebuild v (scalarNorm v)⁻¹=v⁻¹ := by
  have cn (n : C) : (⟨n.re*(normC n)⁻¹,-n.im*(normC n)⁻¹⟩ : C)=n⁻¹ := by
    ext <;> simp only [QuadraticAlgebra.re_inv,QuadraticAlgebra.im_inv,normC_eq] <;> ring
  dsimp only [rebuild,scalarNorm]
  rw [cn]
  ext <;> simp only [QuadraticAlgebra.re_inv,QuadraticAlgebra.im_inv,normK_eq] <;> ring

theorem zip_rebuild (values : List K) :
    List.zipWith rebuild values (values.map fun v=>(scalarNorm v)⁻¹)=
      values.map fun v=>v⁻¹ := by
  induction values with
  | nil => rfl
  | cons v values ih => simp only [List.map_cons,List.zipWith_cons_cons,rebuild_correct,ih]

/-- Both arrays use the already proved checked prefix/backward batch. The
joined source shares their final inverse; `shared_product_seeds` proves those
two initial seeds, and `joined_eq_separate` preserves failures as well. -/
def checked (values : List K) (base : List M) : Option (List K × List M) :=
  if values=[] ∨ (0 : K)∈values then none else do
    let (inverses,baseInverses) ← JoinedInverse.separate (values.map scalarNorm) base
    pure (List.zipWith rebuild values inverses,baseInverses)

theorem checked_spec (values : List K) (base : List M) :
    checked values base =
      if values=[] ∨ (0 : K)∈values ∨ base=[] ∨ (0 : M)∈base then none
      else some (values.map (fun v=>v⁻¹),base.map (fun v=>v⁻¹)) := by
  have nz : (0 : M)∈values.map scalarNorm ↔ (0 : K)∈values := by
    constructor
    · intro h
      obtain ⟨v,hv,hz⟩ := List.mem_map.mp h
      exact (scalarNorm_zero_iff v).mp hz ▸ hv
    · intro h
      exact List.mem_map.mpr ⟨0,h,(scalarNorm_zero_iff 0).mpr rfl⟩
  unfold checked JoinedInverse.separate
  rw [JoinedInverse.checked_correct,JoinedInverse.checked_correct]
  by_cases he : values=[] <;> by_cases hz : (0 : K)∈values <;>
    by_cases hb : base=[] <;> by_cases hzb : (0 : M)∈base <;>
    simp [he,hz,hb,hzb,nz,List.map_map,Function.comp_def,zip_rebuild]

theorem queried_zero_reject (values : List K) (base : List M)
    (zero : (0 : K)∈values) : checked values base=none := by
  rw [checked_spec]
  simp only [zero,true_or,or_true,ite_true]

theorem success_values (values : List K) (base : List M) (out : List K × List M)
    (success : checked values base=some out) :
    (0 : K)∉values ∧ out.1=values.map (fun v=>v⁻¹) ∧
      out.2=base.map (fun v=>v⁻¹) := by
  rw [checked_spec] at success
  split at success
  · contradiction
  · rename_i h
    have same := Option.some.inj success
    subst out
    exact ⟨fun hz=>h (Or.inr (Or.inl hz)),rfl,rfl⟩

section LineCoefficients
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- Source five norm coefficients with the same t=2*x²-1 buffer. The half
operation's canonical machine range is separately proved in LineNorm. -/
def lineFour (r a b c d e f x y : F) :=
  let nc := ChordNorm.norm r e f
  let half := (ChordNorm.norm r c d-nc)/2
  LineNorm.four ((ChordNorm.norm r a b+nc+half)+half*LineNorm.line x)
    (ChordNorm.polar r a b c d*x) (ChordNorm.polar r a b e f*y)
    (ChordNorm.polar r c d e f*(x*y))

theorem lineFour_norms (r a b c d e f x y : F) (circle : x^2+y^2=1) :
    lineFour r a b c d e f x y=
    (ChordNorm.norm r (a+c*x+e*y) (b+d*x+f*y),
     ChordNorm.norm r (a+c*x-e*y) (b+d*x-f*y),
     ChordNorm.norm r (a-c*x-e*y) (b-d*x-f*y),
     ChordNorm.norm r (a-c*x+e*y) (b-d*x+f*y)) := by
  unfold lineFour
  have hh : 2*((ChordNorm.norm r c d-ChordNorm.norm r e f)/2)=
      ChordNorm.norm r c d-ChordNorm.norm r e f := by field_simp
  rw [LineNorm.four_line (ChordNorm.norm r a b+ChordNorm.norm r e f)
    (ChordNorm.norm r c d-ChordNorm.norm r e f)
    ((ChordNorm.norm r c d-ChordNorm.norm r e f)/2) x
    (ChordNorm.polar r a b c d*x) (ChordNorm.polar r a b e f*y)
    (ChordNorm.polar r c d e f*(x*y)) hh]
  exact (CircleNorm.four_slots r a b c d e f x y circle).symm

end LineCoefficients

#print axioms scalarNorm_zero_iff
#print axioms rebuild_correct
#print axioms checked_spec
#print axioms queried_zero_reject
#print axioms success_values
#print axioms lineFour_norms
end
end AspisV8.QueriedInverse
