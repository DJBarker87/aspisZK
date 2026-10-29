import R1Z.PV_RunJoin_SourceLength48
import R1Z.PV_RunJoin_RoundInstalled48
import R1Z.PV_RunJoin_FoldInstalled48
import R1Z.PV_RunJoin_EncodedInstalled48
import R1Z.PV_RunJoin_OpeningEncoded44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FirstArithmetic48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (q w : Nat → Raw)
    (hq : ∀ j,j<1024 → canonical (q j)) (hw : ∀ j,j<1024 → canonical (w j))
    (a : Raw) (ha : canonical a) :
    ∃ (c0 q1 w1 : Nat → Raw) (vq vw : alloc.vec.Vec W) (bytes : alloc.vec.Vec U8)
      (hcc : ∀ j,j<7 → canonical (c0 j)),
      @prover.round (types base) (selected base heap box ops)
        (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))=ok (array 7#usize c0) ∧
      ProverCommitRoundScaled48.run 256 (sourceArray 1024#usize q) (sourceArray 1024#usize w)=
        ok (List.ofFn (fun i : Fin 7 => source (c0 i.val))) ∧
      @prover.fold (types base) (selected base heap box ops) (Array.to_slice (array 1024#usize q))
        (current (source a)) false=ok vq ∧
      @prover.fold (types base) (selected base heap box ops) (Array.to_slice (array 1024#usize w))
        (current (source a)) true=ok vw ∧
      Array.to_slice (array 256#usize q1)=alloc.vec.Vec.deref vq ∧
      Array.to_slice (array 256#usize w1)=alloc.vec.Vec.deref vw ∧
      (∀ j,j<256 → canonical (q1 j) ∧ canonical (w1 j)) ∧
      @prover.encoded_slice (types base) (selected base heap box ops)
        (Array.to_slice (array 7#usize c0))=ok bytes ∧
      bytes.val.map PV_RunJoin_WideImage43.byte=ProverCommitOpeningBytes49.stream 7 c0 hcc := by
  obtain ⟨c0,hc0,hm0,hcc⟩ := @PV_RunJoin_RoundAssociation44.complete (types base) ops 1024#usize (by decide) q w hq hw
  obtain ⟨q1,vq,hq1,hmq,hiq,hcq,hdq⟩ := @PV_RunJoin_PrimalFirst44.complete (types base) ops q hq a ha
  obtain ⟨w1,vw,hw1,hmw,hiw,hcw,hdw⟩ := @PV_RunJoin_DualFirst44.complete (types base) ops w hw a ha
  obtain ⟨bytes,hbytes,himage⟩ := @PV_RunJoin_EncodedImage43.encode (types base) ops 7#usize c0 hcc (by scalar_tac)
  refine ⟨c0,q1,w1,vq,vw,bytes,hcc,?_,hm0,?_,?_,hiq,hiw,fun j hj => ⟨hcq j hj,hcw j hj⟩,?_,himage⟩
  · rw [PV_RunJoin_RoundInstalled48.complete base heap box ops _ _ (@PV_RunJoin_SourceLength48.first (types base) q)]
    exact hc0
  · rw [PV_RunJoin_FoldInstalled48.complete base heap box ops _ _ false (@PV_RunJoin_SourceLength48.first (types base) q)]
    exact hq1
  · rw [PV_RunJoin_FoldInstalled48.complete base heap box ops _ _ true (@PV_RunJoin_SourceLength48.first (types base) w)]
    exact hw1
  · rw [PV_RunJoin_EncodedInstalled48.complete base heap box ops]
    exact hbytes
#print axioms complete
end R1Z.PV_RunJoin_FirstArithmetic48
