import R1Z.PV_RunJoin_OpeningKernel44
import R1Z.PV_RunJoin_EncodedImage43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningEncoded44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem source_values (n : Usize) (p : Nat → Raw) :
    Array.to_slice (array n p) = PV_RunJoin_EncodedImage43.values n p := by rfl

/-- All three complete actual encoders consume the retained opening kernel
outputs in order. The constructor/transcript and publication joins remain separate. -/
theorem complete (ops : ExternalFuns) (q w : Nat → Raw)
    (hq : ∀ j, j < 1024 → canonical (q j)) (hw : ∀ j, j < 1024 → canonical (w j))
    (a b : Raw) (ha : canonical a) (hb : canonical b) :
    ∃ (c0 q1 c1 fin : Nat → Raw) (vq vf : alloc.vec.Vec W) (bc0 bc1 bfin : alloc.vec.Vec U8)
      (hcc0 : ∀ j, j < 7 → canonical (c0 j)) (hcc1 : ∀ j, j < 7 → canonical (c1 j))
      (hcfin : ∀ j, j < 64 → canonical (fin j)),
      PV_RunJoin_OpeningKernel44.run ops (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))
        (current (source a)) (current (source b)) = .ok (array 7#usize c0,vq,array 7#usize c1,vf) ∧
      ProverCommitOpeningKernel49.run (sourceArray 1024#usize q) (sourceArray 1024#usize w) (source a) (source b) =
        .ok (List.ofFn (fun k : Fin 7 => source (c0 k.val)),sourceArray 256#usize q1,
          List.ofFn (fun k : Fin 7 => source (c1 k.val)),sourceArray 64#usize fin) ∧
      @prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops) (Array.to_slice (array 7#usize c0)) = .ok bc0 ∧
      @prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops) (Array.to_slice (array 7#usize c1)) = .ok bc1 ∧
      @prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops) (alloc.vec.Vec.deref vf) = .ok bfin ∧
      bc0.val.map PV_RunJoin_WideImage43.byte = ProverCommitOpeningBytes49.stream 7 c0 hcc0 ∧
      bc1.val.map PV_RunJoin_WideImage43.byte = ProverCommitOpeningBytes49.stream 7 c1 hcc1 ∧
      bfin.val.map PV_RunJoin_WideImage43.byte = ProverCommitOpeningBytes49.stream 64 fin hcfin := by
  obtain ⟨c0,q1,c1,fin,vq,vf,hrun,hret,hiq,hif,hcc,hcfin⟩ := PV_RunJoin_OpeningKernel44.complete ops q w hq hw a b ha hb
  let hcc0 := fun j hj => (hcc j hj).1
  let hcc1 := fun j hj => (hcc j hj).2
  obtain ⟨bc0,hbc0,himage0⟩ := PV_RunJoin_EncodedImage43.encode ops 7#usize c0 hcc0 (by scalar_tac)
  obtain ⟨bc1,hbc1,himage1⟩ := PV_RunJoin_EncodedImage43.encode ops 7#usize c1 hcc1 (by scalar_tac)
  obtain ⟨bfin,hbfin,himagefin⟩ := PV_RunJoin_EncodedImage43.encode ops 64#usize fin hcfin (by scalar_tac)
  refine ⟨c0,q1,c1,fin,vq,vf,bc0,bc1,bfin,hcc0,hcc1,hcfin,hrun,hret,?_,?_,?_,himage0,himage1,himagefin⟩
  · simpa only [source_values] using hbc0
  · simpa only [source_values] using hbc1
  · rw [← hif,source_values]
    exact hbfin
#print axioms source_values
#print axioms complete
end R1Z.PV_RunJoin_OpeningEncoded44
