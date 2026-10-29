import R1Z.PV_RunJoin_FirstArithmetic48
import R1Z.ProverCommitPrimalModel49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FirstModel49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (q w : Nat → Raw) (hq : ∀ j,j<1024 → canonical (q j)) (hw : ∀ j,j<1024 → canonical (w j))
    (a : Raw) (ha : canonical a) :
    ∃ (c0 q1 w1 : Nat → Raw) (vq vw : alloc.vec.Vec W) (bytes : alloc.vec.Vec U8)
      (hc0 : ∀ j,j<7 → canonical (c0 j)),
      @prover.round (types base) (selected base heap box ops)
        (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))=ok (array 7#usize c0) ∧
      @prover.encoded_slice (types base) (selected base heap box ops) (Array.to_slice (array 7#usize c0))=ok bytes ∧
      @prover.fold (types base) (selected base heap box ops) (Array.to_slice (array 1024#usize q))
        (current (source a)) false=ok vq ∧
      @prover.fold (types base) (selected base heap box ops) (Array.to_slice (array 1024#usize w))
        (current (source a)) true=ok vw ∧
      Array.to_slice (array 256#usize q1)=alloc.vec.Vec.deref vq ∧
      Array.to_slice (array 256#usize w1)=alloc.vec.Vec.deref vw ∧
      (∀ j,j<256 → canonical (q1 j) ∧ canonical (w1 j)) ∧
      (∀ i : Fin 256,value (q1 i.val)=AspisR1.RoundPairing.primalFold (value a)
        (fun j : Fin 1024 => value (q j.val)) i) ∧
      (∀ i : Fin 256,value (w1 i.val)=AspisR1.RoundPairing.dualFold (value a)
        (fun j : Fin 1024 => value (w j.val)) i) ∧
      bytes.val.map PV_RunJoin_WideImage43.byte=ProverCommitOpeningBytes49.stream 7 c0 hc0 := by
  obtain ⟨c0,_,_,_,_,bytes,hc0,hround,hmround,_,_,_,_,_,hencode,hbytes⟩ :=
    PV_RunJoin_FirstArithmetic48.complete base heap box ops q w hq hw a ha
  obtain ⟨q1,vq,hqfold,hmq,hiq,hcq,hdq⟩ := @PV_RunJoin_PrimalFirst44.complete (types base) ops q hq a ha
  obtain ⟨w1,vw,hwfold,hmw,hiw,hcw,hdw⟩ := @PV_RunJoin_DualFirst44.complete (types base) ops w hw a ha
  refine ⟨c0,q1,w1,vq,vw,bytes,hc0,hround,hencode,?_,?_,hiq,hiw,fun j hj => ⟨hcq j hj,hcw j hj⟩,?_,hdw,hbytes⟩
  · rw [PV_RunJoin_FoldInstalled48.complete base heap box ops _ _ false (@PV_RunJoin_SourceLength48.first (types base) q)]
    exact hqfold
  · rw [PV_RunJoin_FoldInstalled48.complete base heap box ops _ _ true (@PV_RunJoin_SourceLength48.first (types base) w)]
    exact hwfold
  · intro i
    rw [hdq i.val i.isLt]
    exact ProverCommitPrimalModel49.cell_model 256 q (value a) i
#print axioms complete
end R1Z.PV_RunJoin_FirstModel49
