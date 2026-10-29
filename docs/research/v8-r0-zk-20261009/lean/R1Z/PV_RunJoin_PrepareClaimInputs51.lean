import R1Z.PV_RunJoin_ClaimThread48
import R1Z.PV_RunJoin_PrepareReach50
import R1Z.PV_RunJoin_PrepareTailSuccess48
import R1Z.PV_RunJoin_SemanticClaimPoint50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareClaimInputs51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitSubfieldOps47
open PV_RunJoin_ClaimThread48 (Column)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (out : prover.PreparedOpening)
    (h : @prover.prepare_opening (types base) (selected base heap box ops) variant hash backend sem=ok (.Ok out)) :
    (Canonical (PV_RunJoin_SemanticClaimPoint50.x sem.z) ∧ Canonical (PV_RunJoin_SemanticClaimPoint50.y sem.z)) ∧
    ∃ coeff : alloc.vec.Vec Column,
      @prover.opening_coefficients (types base) (selected base heap box ops) variant
        (alloc.vec.Vec.deref backend.messages)=ok coeff ∧
      @prover.opening_claim_bytes (types base) (selected base heap box ops)
        (alloc.vec.Vec.deref coeff) (PV_RunJoin_SemanticClaimPoint50.point sem.z)=ok out.y1 := by
  obtain ⟨coeff,scp,x,y,weight,tr0,tr1,tr2,claim,gamma,inactive,kappa,ib,q,w,
    hcoeff,hpoint,hx,hy,hclaim,hq,hctor,hi,hib,hmat,hg,hk,htail⟩ :=
    PV_RunJoin_PrepareReach50.complete base heap box ops variant hash backend sem out h
  have actual : PV_RunJoin_SemanticClaimPoint50.run base heap box ops sem.z=
      ok (aspis_core.r0.domain.Point.mk x y) := by
    unfold PV_RunJoin_SemanticClaimPoint50.run
    rw [hpoint]
    simp only [bind_tc_ok,hx,hy]
  have epoint := Result.ok.inj (actual.symm.trans
    (PV_RunJoin_SemanticClaimPoint50.complete base heap box ops sem.z))
  obtain ⟨c0,bytes,a,next,q1,w1,folded,hr,he,hs,hfq,hfw,hd,hfields⟩ :=
    PV_RunJoin_PrepareTailSuccess48.complete base heap box ops variant hash backend sem tr2 claim gamma inactive kappa
      (alloc.vec.Vec.deref q) (alloc.vec.Vec.deref w) out htail
  rcases hfields with ⟨hb,hm,ht,hyout,hgamma,hinactive,hkappa,halpha,hbc,hqo,hwo,hfo⟩
  refine ⟨PV_RunJoin_SemanticClaimPoint50.canonical sem.z,coeff,hcoeff,?_⟩
  rw [←epoint,hyout]
  exact hclaim
#print axioms complete
end R1Z.PV_RunJoin_PrepareClaimInputs51
