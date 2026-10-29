import R1Z.PV_RunJoin_GammaArray49
import R1Z.PV_RunJoin_MaterialCanonical49
import R1Z.PV_RunJoin_MaterialTail49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ProducedTail49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (Weight toWeight)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_CoefficientsWeight46 (Column messages)
open PV_RunJoin_FoldCell44 (array)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (c : Nat → Nat → Raw) (hc : ∀ l,l<29 → ∀ j,j<1024 → canonical (c l j))
    (p : Nat → Old.Q) (hp : ∀ i,i<10 → Canonical (p i))
    (x0 y0 x1 y1 : Old.Q) (hx0 : Canonical x0) (hy0 : Canonical y0) (hx1 : Canonical x1) (hy1 : Canonical y1)
    (g k : Raw) (hg : canonical g) (hk : canonical k)
    (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (tr : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (claimBytes : alloc.vec.Vec U8) (inactive : W) :
    let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
    ∃ (coefficients : alloc.vec.Vec Column) (qout : alloc.vec.Vec W) (kw : Weight)
      (q w c0 : Nat → Raw) (bytes : alloc.vec.Vec U8) (hc0 : ∀ j,j<7 → canonical (c0 j)),
      @prover.opening_coefficients (types base) (selected base heap box incoming) .S2
        (messages (fun l j => current (source (c l j))))=ok coefficients ∧
      @prover.opening_batch (types base) (selected base heap box incoming) (alloc.vec.Vec.deref coefficients)
        (current (source g))=ok qout ∧
      @ExternalFuns.op252 (types base) (selected base heap box incoming) .S2
        (PV_RunJoin_MaterialInputs49.alpha p) (PV_RunJoin_MaterialInputs49.points x0 y0 x1 y1)=
        (do let _ ← box .S2 (PV_RunJoin_MaterialInputs49.alpha p) (PV_RunJoin_MaterialInputs49.points x0 y0 x1 y1)
            ok (.Ok (toWeight kw))) ∧
      (∀ j,j<1024 → canonical (q j) ∧ canonical (w j)) ∧
      @PV_RunJoin_MaterialContinuation49.run (types base) (selected base heap box incoming)
        (@ExternalFuns.op251 (types base) (selected base heap box incoming) (toWeight kw) (current (source k)))
        (@PV_RunJoin_PrepareTail48.run (types base) (selected base heap box incoming) variant hash backend sem
          tr claimBytes (current (source g)) inactive (current (source k)) (alloc.vec.Vec.deref qout))=
        (do let event ← heap (toWeight kw) (current (source k))
            match event with
            | .denied => ok (.Err .Allocation)
            | .supplied => @PV_RunJoin_PrepareTailAssociation48.retained (types base) (selected base heap box incoming)
                variant hash backend sem tr claimBytes (current (source g)) inactive (current (source k)) bytes
                (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))
                (@prover.fold (types base) (@ProverRwP6BodyCandidate.selected (types base) incoming))) ∧
      ProverCommitRoundScaled48.run 256 (sourceArray 1024#usize q) (sourceArray 1024#usize w)=
        ok (List.ofFn (fun i : Fin 7 => source (c0 i.val))) ∧
      bytes.val.map PV_RunJoin_WideImage43.byte=ProverCommitOpeningBytes49.stream 7 c0 hc0 := by
  dsimp only
  let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
  obtain ⟨coefficients,q,qout,hcoeff,hv,hl,hbatch,hqmodel,hqi,hcq⟩ :=
    PV_RunJoin_GammaArray49.complete base heap box ops c g hc hg
  obtain ⟨kw,hs,hctor,hmat⟩ := PV_RunJoin_MaterialCanonical49.complete base heap box incoming p hp
    x0 y0 x1 y1 hx0 hy0 hx1 hy1
  obtain ⟨w,hwmodel,hcw,hdw,hw⟩ := hmat k hk
  obtain ⟨c0,bytes,hc0,htail,hround,hbytes⟩ := PV_RunJoin_MaterialTail49.complete base heap box incoming
    variant hash backend sem tr claimBytes (current (source g)) inactive (current (source k)) q w hcq hcw
    (heap (toWeight kw) (current (source k)))
  refine ⟨coefficients,qout,kw,q,w,c0,bytes,hc0,hcoeff,hbatch,hctor,fun j hj => ⟨hcq j hj,hcw j hj⟩,?_,hround,hbytes⟩
  rw [hw]
  have hq : alloc.vec.Vec.deref qout=Array.to_slice (array 1024#usize q) := hqi.symm
  rw [hq]
  exact htail
#print axioms complete
end R1Z.PV_RunJoin_ProducedTail49
