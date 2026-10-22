import R1Z.ProverCommitStoredProduct49
import R1Z.ProverCommitPointRowsOutput49
import R1Z.ProverCommitCircleCaller49
/-! The actual initialized point/circle matrices feed the actual stored
lookups and multiplication loop. Pure value composition, not a call-count law. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitStoredCaller49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitCircleRows49 ProverCommitStoredProduct49
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

theorem array_congr (size : Usize) (a b : Nat → Old.Q) (h : ∀ i, i<size.val → a i=b i) :
    ProverCommitQArray48.array size a=ProverCommitQArray48.array size b := by
  apply Subtype.ext
  apply congrArg List.ofFn
  funext i
  rw [h i.val i.isLt]

def point (p : Array field.QM31 10#usize) (j : Usize) : Result field.QM31 := do
  let rows ← point_rows.all p
  stored.product rows j 0#usize 5#u8 field.QM31.ONE

theorem point_exact (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i)) (j : Usize) (hj : j.val<1024) :
    ∃ z : Old.Q, point (ProverCommitQArray48.array 10#usize p) j=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=AspisR0.Opening.eqWeight
        (ProverCommitPointWeight49.reverse (fun i : Fin 10 => decode (p i.val)))
        (AspisR1.rowEquiv.symm ⟨j.val,hj⟩) := by
  obtain ⟨rows,hrows,hcrows,heq⟩ := ProverCommitPointRowsOutput49.all p hp
  have harr : ProverCommitQArray48.array 5#usize (selected rows j)=
      ProverCommitQArray48.array 5#usize
        (ProverCommitPointWeight49.selected (fun i : Fin 10 => p i.val) (fun i => hp i.val i.isLt) ⟨j.val,hj⟩) := by
    apply array_congr
    intro i hi
    change i<5 at hi
    rw [selected,heq ⟨i,hi⟩]
    simp only [ProverCommitPointRows49.target,ProverCommitPointWeight49.selected,Fin.val_mk,dif_pos hi]
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitPointWeight49.point_raw_exact
    (fun i : Fin 10 => p i.val) (fun i => hp i.val i.isLt) ⟨j.val,hj⟩
  refine ⟨z,?_,hcz,hdz⟩
  rw [point,hrows]
  simp only [bind_tc_ok]
  rw [binding rows j 5 0#usize 5#u8 rfl (by decide),harr]
  exact hz

def circle (x y : field.QM31) (j : Usize) : Result field.QM31 := do
  let rows ← factors.circle_rows x y
  stored.product rows j 0#usize 5#u8 field.QM31.ONE

theorem circle_exact (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) (j : Usize) (hj : j.val<1024) :
    ∃ z : Old.Q, circle (ProverCommitNativeQ48.source x) (ProverCommitNativeQ48.source y) j=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=ProverCommitEval47.messageEval (Pi.single (⟨j.val,hj⟩ : Fin 1024) 1) (decode x) (decode y) := by
  have hr := (ProverCommitCircleWeight49.rows_spec x y hx hy).1
  have harr : ProverCommitQArray48.array 5#usize (selected (ProverCommitCircleWeight49.rows x y hx hy) j)=
      ProverCommitQArray48.array 5#usize (ProverCommitCircleWeight49.selected x y hx hy ⟨j.val,hj⟩) := by
    apply array_congr
    intro i hi
    change i<5 at hi
    simp only [selected,ProverCommitCircleWeight49.selected,dif_pos hi]
  obtain ⟨z,hz,hcz,hdz,_⟩ := ProverCommitCircleCaller49.raw_message x y hx hy ⟨j.val,hj⟩
  refine ⟨z,?_,hcz,hdz⟩
  rw [circle,hr]
  simp only [bind_tc_ok]
  rw [binding _ j 5 0#usize 5#u8 rfl (by decide),harr]
  exact hz

#print axioms array_congr
#print axioms point_exact
#print axioms circle_exact
end R1Z.ProverCommitStoredCaller49
