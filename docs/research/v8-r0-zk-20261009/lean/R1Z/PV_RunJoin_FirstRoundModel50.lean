import R1Z.PV_RunJoin_FirstArithmetic48
import R1Z.PV_RunJoin_RawImage50
import R1Z.ProverCommitRoundModel49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FirstRoundModel50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (q w : Nat → Raw) (hq : ∀ j,j<1024 → canonical (q j)) (hw : ∀ j,j<1024 → canonical (w j)) :
    ∃ (c0 : Nat → Raw) (bytes : alloc.vec.Vec U8) (hc0 : ∀ j,j<7 → canonical (c0 j)),
      @prover.round (types base) (selected base heap box ops)
        (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))=ok (array 7#usize c0) ∧
      @prover.encoded_slice (types base) (selected base heap box ops) (Array.to_slice (array 7#usize c0))=ok bytes ∧
      ProverCommitRoundScaled48.run 256 (sourceArray 1024#usize q) (sourceArray 1024#usize w)=
        ok (List.ofFn (fun i : Fin 7 => source (c0 i.val))) ∧
      (∀ i : Fin 7,value (c0 i.val)=(AspisR1.RoundPairing.roundPolynomial (n:=256)
        (fun j => value (q j.val)) (fun j => value (w j.val))).coeff i.val) ∧
      bytes.val.map PV_RunJoin_WideImage43.byte=ProverCommitOpeningBytes49.modelStream 7
        (fun i => (AspisR1.RoundPairing.roundPolynomial (n:=256)
          (fun j => value (q j.val)) (fun j => value (w j.val))).coeff i.val) := by
  obtain ⟨c0,q1,w1,vq,vw,bytes,hcc,hr,hm,hfq,hfw,hiq,hiw,hc,henc,hbytes⟩ :=
    PV_RunJoin_FirstArithmetic48.complete base heap box ops q w hq hw ProverCommitGamma48.zero
      ProverCommitGamma48.zero_canonical
  obtain ⟨model,hm',hcm,hdm⟩ := ProverCommitRoundModel49.coefficients 256 (by decide) q w hq hw
  have eq := PV_RunJoin_RawImage50.list 7 c0 model (Result.ok.inj (hm.symm.trans hm'))
  have meaning : ∀ i : Fin 7,value (c0 i.val)=(AspisR1.RoundPairing.roundPolynomial (n:=256)
      (fun j => value (q j.val)) (fun j => value (w j.val))).coeff i.val := by
    intro i
    rw [eq i]
    exact hdm i
  refine ⟨c0,bytes,hcc,hr,henc,hm,meaning,?_⟩
  rw [hbytes]
  exact ProverCommitOpeningBytes49.stream_image _ _ _ _ meaning
#print axioms complete
end R1Z.PV_RunJoin_FirstRoundModel50
