import R1Z.ProverCommitFactorProduct49
import R0.OpeningWeights
/-! The source point-factor constructor and full five-factor product give the
transported Boolean opening weight. No factor/model-image premise is assumed.
Statement-point construction and complete Weights initialization remain callers. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPointWeight49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitPointTensor49
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open scoped BigOperators

variable (p : Fin 10 → Old.Q) (hp : ∀ i, Canonical (p i))

def a (d : Fin 5) : Fin 10 := ⟨9-2*(d18Tau d).val,by have := (d18Tau d).isLt;omega⟩
def b (d : Fin 5) : Fin 10 := ⟨8-2*(d18Tau d).val,by have := (d18Tau d).isLt;omega⟩

def row (d : Fin 5) : Nat → Old.Q :=
  Classical.choose (ProverCommitFactors49.point_exact (p (a d)) (p (b d)) (hp _) (hp _))

theorem row_spec (d : Fin 5) :
    factors.point (ProverCommitNativeQ48.source (p (a d))) (ProverCommitNativeQ48.source (p (b d)))=
      ok (ProverCommitQArray48.array 4#usize (row p hp d)) ∧
      (∀ k, k<4 → Canonical (row p hp d k)) ∧
      ∀ k : Fin 4, decode (row p hp d k.val)=pairFactor (decode (p (a d))) (decode (p (b d))) k.val :=
  Classical.choose_spec (ProverCommitFactors49.point_exact (p (a d)) (p (b d)) (hp _) (hp _))

def selected (j : Fin 1024) (i : Nat) : Old.Q :=
  if h : i<5 then row p hp ⟨i,h⟩ ((j.val/4^i)%4) else zero

theorem selected_canonical (j : Fin 1024) (i : Nat) (hi : i<5) : Canonical (selected p hp j i) := by
  rw [selected,dif_pos hi]
  exact (row_spec p hp ⟨i,hi⟩).2.1 _ (Nat.mod_lt _ (by decide))

theorem selected_value (j : Fin 1024) (d : Fin 5) :
    decode (selected p hp j d.val)=pairFactor (decode (p (a d))) (decode (p (b d))) ((j.val/4^d.val)%4) := by
  rw [selected,dif_pos d.isLt]
  exact (row_spec p hp d).2.2 ⟨(j.val/4^d.val)%4,Nat.mod_lt _ (by decide)⟩

theorem tensor_exact (j : Fin 1024) :
    ∃ z : Old.Q, factors.product (ProverCommitQArray48.array 5#usize (selected p hp j))
        0#usize 5#u8 field.QM31.ONE=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=tensorPoint (fun i => decode (p i)) j := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitFactorProduct49.raw_exact (selected p hp j) (selected_canonical p hp j)
  refine ⟨z,hz,hcz,?_⟩
  rw [hdz]
  simp only [selected_value,tensorPoint,a,b]

def reverse (p : Fin 10 → QM31Exact) (i : Fin 10) : QM31Exact := p ⟨9-i.val,by have := i.isLt;omega⟩

theorem tensor_model (j : Fin 1024) :
    tensorPoint (fun i => decode (p i)) j=
      AspisR0.Opening.eqWeight (reverse (fun i => decode (p i))) (AspisR1.rowEquiv.symm j) := by
  rw [←rowPoint_eq_tensorPoint]
  have he : AspisR1.rowEquiv.symm j=AspisR1.row j := by
    apply AspisR1.rowEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (AspisR1.row_involutive j).symm
  rw [he]
  rfl

theorem point_raw_exact (j : Fin 1024) :
    ∃ z : Old.Q, factors.product (ProverCommitQArray48.array 5#usize (selected p hp j))
        0#usize 5#u8 field.QM31.ONE=ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=AspisR0.Opening.eqWeight (reverse (fun i => decode (p i))) (AspisR1.rowEquiv.symm j) := by
  obtain ⟨z,hz,hcz,hdz⟩ := tensor_exact p hp j
  exact ⟨z,hz,hcz,hdz.trans (tensor_model p j)⟩

#print axioms row_spec
#print axioms selected_canonical
#print axioms selected_value
#print axioms tensor_exact
#print axioms tensor_model
#print axioms point_raw_exact
end R1Z.ProverCommitPointWeight49
