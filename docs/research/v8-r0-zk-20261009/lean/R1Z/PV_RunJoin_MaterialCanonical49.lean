import R1Z.PV_RunJoin_MaterialProducer49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MaterialCanonical49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (Weight toWeight)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48 ProverCommitMix48
open PV_RunJoin_MaterialInputs49 (alpha points)
open scoped BigOperators

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (p : Nat → Old.Q) (hp : ∀ i,i<10 → Canonical (p i))
    (x0 y0 x1 y1 : Old.Q) (hx0 : Canonical x0) (hy0 : Canonical y0)
    (hx1 : Canonical x1) (hy1 : Canonical y1) :
    ∃ kw : Weight,
      (toWeight kw).variant=.S2 ∧
      @ExternalFuns.op252 (types base) (selected base heap box ops) .S2 (alpha p) (points x0 y0 x1 y1)=
        (do let _ ← box .S2 (alpha p) (points x0 y0 x1 y1);ok (.Ok (toWeight kw))) ∧
      (∀ k : Raw,canonical k → ∃ w : Nat → Raw,
        ProverCommitWeightsMaterial53.run (ProverCommitQArray48.array 10#usize p)
          (ProverCommitNativeQ48.source x0) (ProverCommitNativeQ48.source y0)
          (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1) (source k)=ok (sourceArray 1024#usize w) ∧
        (∀ j,j<1024 → canonical (w j)) ∧
        (∀ j : Fin 1024,value (w j.val)=∑ r : Fin 7,value k^r.val*ProverCommitWideRows49.rows
          (fun i => ProverCommitValueRange47.embed (ProverCommitSuccessorPoint49.decoded p i))
          (ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode x0))
          (ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode y0))
          (ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode x1))
          (ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode y1)) j r) ∧
        @ExternalFuns.op251 (types base) (selected base heap box ops) (toWeight kw) (ProverRwDictionaryTower.fromW (source k))=
          PV_RunJoin_MaterialRun49.outcome (heap (toWeight kw) (ProverRwDictionaryTower.fromW (source k)))
            (ok (sourceArray 1024#usize w))) := by
  obtain ⟨kw,hs,hctor,hmat⟩ := PV_RunJoin_MaterialProducer49.complete base heap box ops p x0 y0 x1 y1
  refine ⟨kw,hs,hctor,?_⟩
  intro k hk
  obtain ⟨w,hw,hcw,hdw⟩ := ProverCommitWeightsMaterial53.exact_result p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 k hk
  refine ⟨w,hw,hcw,hdw,?_⟩
  rw [hmat,hw]
#print axioms complete
end R1Z.PV_RunJoin_MaterialCanonical49
