import AspisR1ProducerRelease47.KernelCallers49
import R1Z.ProverCommitNativePower49
import R1Z.ProverCommitSampleTail49
import R1Z.ProverCommitInactiveRow49
import R0P.SemView
/-! The complete raw Libra column, including both geometric runs and its
zero suffix. The source coefficient power is not supplied as a hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitLibra49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitSubtraction47 (one one_canonical)

def entries (a b : Old.Q) : Nat → Old.Q := fun k => if k=0 then a else b

def run (a b : Old.Q) (j : Usize) : Result field.QM31 :=
  extras.libra (ProverCommitQArray48.array 2#usize (entries a b)) j

theorem exact_result (a b : Old.Q) (ha : Canonical a) (hb : Canonical b) (j : Usize) :
    ∃ z : Old.Q, run a b j=ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=(if j.val<28 then decode a^j.val
        else if j.val<56 then decode b^(j.val-28) else 0) := by
  by_cases hj : j.val<56
  · have hs : j<56#usize := by scalar_tac
    obtain ⟨side,hside,hvside⟩ := ProverCommitInactiveRow49.div_value j 28#usize (by decide)
    obtain ⟨ex,hex,hvex⟩ := ProverCommitInactiveRow49.rem_value j 28#usize (by decide)
    change side.val=j.val/28 at hvside
    change ex.val=j.val%28 at hvex
    have sidebound : side.val<2 := by omega
    have castval : (UScalar.cast .U8 ex).val=j.val%28 := by
      have exbound : ex.val<28 := by rw [hvex];exact Nat.mod_lt _ (by decide)
      scalar_tac
    have hcan : Canonical (entries a b side.val) := by
      unfold entries;split <;> assumption
    obtain ⟨z,hz,hcz,hvz⟩ := ProverCommitNativePower49.power _ _ castval (entries a b side.val) one hcan one_canonical
    refine ⟨z,?_,hcz,?_⟩
    · rw [run,extras.libra,if_pos hs]
      simp only [hside,bind_tc_ok]
      rw [ProverCommitQArray48.index _ _ _ sidebound]
      simp only [hex,ProverCommitSampleTail49.source_one,lift,bind_tc_ok]
      exact hz
    · rw [hvz,ProverCommitSubtraction47.one_decode,one_mul]
      by_cases hsmall : j.val<28
      · have hside0 : side.val=0 := by omega
        simp only [entries,hside0,if_true,if_pos hsmall,Nat.mod_eq_of_lt hsmall]
      · have hside1 : side.val=1 := by omega
        have hmod : j.val%28=j.val-28 := by omega
        simp only [entries,hside1,if_neg (by decide : (1:Nat)≠0),if_neg hsmall,if_pos hj,hmod]
  · have hs : ¬j<56#usize := by scalar_tac
    refine ⟨zero,?_,zero_canonical,?_⟩
    · rw [run,extras.libra,if_neg hs,ProverCommitQArray48.source_zero]
    · simp only [zero_decode,if_neg hj,if_neg (by omega : ¬j.val<28)]

theorem model (alpha : Fin 10 → QM31Exact) (a b z : Old.Q) (j : Fin 1024)
    (ha : decode a=alpha 8) (hb : decode b=alpha 9)
    (hz : decode z=(if j.val<28 then decode a^j.val else if j.val<56 then decode b^(j.val-28) else 0)) :
    decode z=R0P.SemSource.libraWeight alpha j := by
  rw [hz,ha,hb]
  rfl

theorem caller (alpha : Fin 10 → Old.Q) (hc : ∀ i, Canonical (alpha i))
    (j : Usize) (hj : j.val<1024) :
    ∃ z : Old.Q, run (alpha 8) (alpha 9) j=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=R0P.SemSource.libraWeight (fun i => decode (alpha i)) ⟨j.val,hj⟩ := by
  obtain ⟨z,hz,hcz,hdz⟩ := exact_result (alpha 8) (alpha 9) (hc 8) (hc 9) j
  exact ⟨z,hz,hcz,model (fun i => decode (alpha i)) _ _ z ⟨j.val,hj⟩ rfl rfl hdz⟩

#print axioms exact_result
#print axioms model
#print axioms caller
end R1Z.ProverCommitLibra49
