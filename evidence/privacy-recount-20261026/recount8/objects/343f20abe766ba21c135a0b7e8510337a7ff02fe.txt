import R1Z.ProverCommitOpeningFolded54
import R1Z.PV_RunJoin_EncodedImage43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoldedEncoding43
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48 ProverCommitMix48
open ProverCommitValueRange47 (embed)
open ProverCommitSuccessorPoint49 (decoded)
open AspisR1.ExtractedCurrentQM31Exact (decode)
variable [ProverRwFull.ExternalTypes]
variable (c : Nat → Nat → Old.Q) (hc : ∀ l, l<29 → ∀ i, i<1024 → Canonical (c l i))

/-- The retained complete opening producer supplies the folded model leaf;
its converted current source encoding has the exact ordered model bytes.
Association with the current PreparedOpening constructor remains separate. -/
theorem encode (ops : ProverRwFull.ExternalFuns) (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (x0 y0 x1 y1 : Old.Q) (hx0 : Canonical x0) (hy0 : Canonical y0)
    (hx1 : Canonical x1) (hy1 : Canonical y1) (g k a b : Raw)
    (hg : canonical g) (hk : canonical k) (hca : canonical a) (hcb : canonical b)
    (ch : R0Z.HonestView.Challenges Exact)
    (hpoint : (fun i => embed (decoded p i))=R0Z.HonestView.alpha ch)
    (hz0x : embed (decode x0)=(ch.circle 0).1.1)
    (hz0y : embed (decode y0)=(ch.circle 0).1.2)
    (hz1x : embed (decode x1)=(ch.circle 1).1.1)
    (hz1y : embed (decode y1)=(ch.circle 1).1.2)
    (hgch : value g=ch.opening 0) (hkch : value k=ch.opening 1)
    (hach : value a=ch.opening 2) (hbch : value b=ch.opening 3)
    (v : Usize) (u : Fin 65536) (hv : v.val=u.val) :
    ∃ (c0 q1 c1 fin leaf : Nat → Raw) (hcleaf : ∀ s, s<4 → canonical (leaf s))
      (bytes : alloc.vec.Vec U8),
      ProverCommitOpeningFolded54.run c hc (ProverCommitQArray48.array 10#usize p)
        (ProverCommitNativeQ48.source x0) (ProverCommitNativeQ48.source y0)
        (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1)
        (source g) (source k) (source a) (source b) v=
        ok ((List.ofFn (fun i : Fin 7 => source (c0 i.val)),sourceArray 256#usize q1,
          List.ofFn (fun i : Fin 7 => source (c1 i.val)),sourceArray 64#usize fin),sourceArray 4#usize leaf) ∧
      @ProverRwFull.prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops)
        (PV_RunJoin_EncodedImage43.values 4#usize leaf)=ok bytes ∧
      bytes.val.map PV_RunJoin_WideImage43.byte=PhaseLeafEncodingBin.foldedLeaf
        (Batched.q1 AspisR1.rowEquiv ch (ProverCommitGammaCoefficients53.wideTrace c))
        ⟨u.val,by have := u.isLt;omega⟩ := by
  obtain ⟨c0,q1,c1,fin,leaf,hcleaf,hrun,hbytes⟩ :=
    ProverCommitOpeningFolded54.exact_result c hc p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1
      g k a b hg hk hca hcb ch hpoint hz0x hz0y hz1x hz1y hgch hkch hach hbch v u hv
  obtain ⟨bytes,hencode,himage⟩ := PV_RunJoin_EncodedImage43.encode ops 4#usize leaf hcleaf
    (by scalar_tac)
  exact ⟨c0,q1,c1,fin,leaf,hcleaf,bytes,hrun,hencode,himage.trans hbytes⟩
#print axioms encode
end R1Z.PV_RunJoin_FoldedEncoding43
