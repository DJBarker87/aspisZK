import R1Z.ProverCommitOpeningKernel49
import R1Z.ProverCommitWideBytes48
/-! Ordered native encoded-value images of both round polynomials and final
coefficients, after the complete owned opening-kernel caller. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOpeningBytes49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48

def stream (n : Nat) (q : Nat → Raw) (hc : ∀ i, i<n → canonical (q i)) : List UInt8 :=
  (List.ofFn (fun i : Fin n => List.ofFn (ProverCommitWideBytes48.sourceCell (q i.val) (hc i.val i.isLt)))).flatten

def modelStream (n : Nat) (f : Fin n → Exact) : List UInt8 :=
  (List.ofFn (fun i : Fin n => List.ofFn (ProverCommitValueRange47.bytes (f i)))).flatten

theorem stream_image (n : Nat) (q : Nat → Raw) (hc : ∀ i, i<n → canonical (q i))
    (f : Fin n → Exact) (hf : ∀ i : Fin n, value (q i.val)=f i) :
    stream n q hc=modelStream n f := by
  unfold stream modelStream
  congr 2
  funext i
  rw [ProverCommitWideBytes48.source_image,hf i]

attribute [local irreducible] value sourceArray source List.ofFn

theorem exact_images (q w : Nat → Raw)
    (hq : ∀ i, i<1024 → canonical (q i)) (hw : ∀ i, i<1024 → canonical (w i))
    (a b : Raw) (ha : canonical a) (hb : canonical b) :
    ∃ (c0 q1 c1 fin : Nat → Raw) (hc0 : ∀ k, k<7 → canonical (c0 k))
      (hc1 : ∀ k, k<7 → canonical (c1 k)) (hcfin : ∀ i, i<64 → canonical (fin i)),
      ProverCommitOpeningKernel49.run (sourceArray 1024#usize q) (sourceArray 1024#usize w) (source a) (source b)=
        ok (List.ofFn (fun k : Fin 7 => source (c0 k.val)),sourceArray 256#usize q1,
          List.ofFn (fun k : Fin 7 => source (c1 k.val)),sourceArray 64#usize fin) ∧
      stream 7 c0 hc0=modelStream 7 (fun k => (AspisR1.RoundPairing.roundPolynomial (n:=256)
        (fun j => value (q j.val)) (fun j => value (w j.val))).coeff k.val) ∧
      stream 7 c1 hc1=modelStream 7 (fun k => (AspisR1.RoundPairing.roundPolynomial (n:=64)
        (AspisR1.RoundPairing.primalFold (value a) (fun j : Fin 1024 => value (q j.val)))
        (AspisR1.RoundPairing.dualFold (value a) (fun j : Fin 1024 => value (w j.val)))).coeff k.val) ∧
      stream 64 fin hcfin=modelStream 64 (fun i => AspisR1.RoundPairing.primalFold (value b)
        (AspisR1.RoundPairing.primalFold (value a) (fun j : Fin 1024 => value (q j.val))) i) := by
  obtain ⟨c0,q1,w1,c1,fin,hrun,hcc,hcf,hcfin,hq1,hw1,hd0,hd1,hdfin⟩ :=
    ProverCommitOpeningKernel49.exact_result q w hq hw a b ha hb
  refine ⟨c0,q1,c1,fin,(fun k hk => (hcc k hk).1),(fun k hk => (hcc k hk).2),hcfin,hrun,?_,?_,?_⟩
  · exact stream_image _ _ _ _ hd0
  · exact stream_image _ _ _ _ hd1
  · exact stream_image _ _ _ _ hdfin

#print axioms stream_image
#print axioms exact_images
end R1Z.ProverCommitOpeningBytes49
