import R1Z.ProverCommitStatementPoints49
import R1Z.ProverCommitPointWeight49
/-! Compose statement-point production with the three complete point-weight
factor products, without a supplied statement-point or factor-value identity. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPointCaller49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitSuccessorPoint49
open R0P.SemSource
open AspisR1.ExtractedCurrentQM31Exact (decode)

theorem point_weights (p : Nat → Old.Q) (hp : ∀ k, k<10 → Canonical (p k)) (j : Fin 1024) :
    ∃ pts : Fin 3 → Nat → Old.Q,
      points.all (ProverCommitQArray48.array 10#usize p)=ok (Array.make 3#usize
        [ProverCommitQArray48.array 10#usize (pts 0),ProverCommitQArray48.array 10#usize (pts 1),
         ProverCommitQArray48.array 10#usize (pts 2)]) ∧
      ∃ hcanon : ∀ i k, k<10 → Canonical (pts i k),
        ∀ i : Fin 3, ∃ z : Old.Q,
          factors.product (ProverCommitQArray48.array 5#usize
              (ProverCommitPointWeight49.selected (fun k : Fin 10 => pts i k.val)
                (fun k => hcanon i k.val k.isLt) j))
              0#usize 5#u8 field.QM31.ONE=ok (ProverCommitNativeQ48.source z) ∧
          Canonical z ∧ decode z=AspisR0.Opening.eqWeight
            (openingPoints (decoded p) i) (AspisR1.rowEquiv.symm j) := by
  obtain ⟨s,a,hpoints,hcs,hca,hmodel⟩ := ProverCommitStatementPoints49.points_exact p hp
  let pts : Fin 3 → Nat → Old.Q := ![p,s,a]
  have hc : ∀ i k, k<10 → Canonical (pts i k) := by
    intro i k hk
    fin_cases i
    · exact hp k hk
    · exact hcs k hk
    · exact hca k hk
  refine ⟨pts,hpoints,hc,?_⟩
  intro i
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitPointWeight49.point_raw_exact
    (fun k : Fin 10 => pts i k.val) (fun k => hc i k.val k.isLt) j
  refine ⟨z,hz,hcz,?_⟩
  rw [hdz]
  have he : ProverCommitPointWeight49.reverse (fun k : Fin 10 => decode (pts i k.val))=
      openingPoints (decoded p) i := hmodel i
  rw [he]

#print axioms point_weights
end R1Z.ProverCommitPointCaller49
