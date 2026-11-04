import R1Z.PhaseBuilderDependenciesBin
import R1Z.PhaseCausalityBin

/-! Constructed leaf functions from the existing masked trace and q1 map.
Encoders are parameters because the privacy tree has no sourced field-to-byte
encoder. Source equality for these parameters is not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseLeafConstructionBin
open R0P R0P.SemSource R0Z R0Z.JointView R0Z.FsStatement R0Z.HonestView
  R0Z.MaskLayout R1Z.Batched R1Z.GamesR1 R1Z.GamesR1PBin
  R1Z.PhaseScheduleBin R1Z.PhaseLocalityBin R1Z.TranscriptR1
  R1Z.PhaseBuilderDependenciesBin R1Z.PhaseCausalityBin

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

structure LeafEncoding (K : Type) where
  c1 : (Fin 27 → Fin 1024 → K) → Fib → List UInt8
  c2 : (Fin 2 → Fin 1024 → K) → Fib → List UInt8
  folded : (Fin 256 → K) → Fib → List UInt8

def leafVal (enc : LeafEncoding K) (B : PackBasis F) (h : HonestProver K)
    (w : h.Instance) (x : Statement K CommitHandle) (τ : Tape K F)
    (ch : R0Z.HonestView.Challenges K) (T : Fin 3) (u : Fib) : List UInt8 :=
  if T.val = 0 then
    enc.c1 (fun c => applyAff B (applyEligible (h.build w) τ.2) τ.1 (c1Column c)) u
  else if T.val = 1 then
    enc.c2 (fun c => applyAff B (prepare x.1 (applyEligible (h.build w) τ.2) ch) τ.1
      ⟨26 + c.val, by omega⟩) u
  else
    enc.folded (q1 h.transport ch
      (applyAff B (prepare x.1 (applyEligible (h.build w) τ.2) ch) τ.1)) u

theorem leaf_local (enc : LeafEncoding K) (B : PackBasis F) (h : HonestProver K)
    (w : h.Instance) (x : Statement K CommitHandle) (τ : Tape K F)
    (W : R1Wire K CommitHandle Aux) (hd : DecodeLocal W.dec)
    (tr tr' : TRead → OracleAnswer) (T : Fin 3) (u : Fib)
    (he : SqAgree (treeBase T + 6) tr tr') :
    leafVal enc B h w x τ (chOf W tr) T u = leafVal enc B h w x τ (chOf W tr') T u := by
  unfold leafVal
  by_cases h0 : T.val = 0
  · simp only [h0, if_true]
  · by_cases h1 : T.val = 1
    · have hp := prepared_at_c2 W hd x.1 (h.build w) B τ tr tr'
        (by simpa [treeBase, h0, h1] using he)
      simp only [h0, h1, if_false, if_true, hp]
    · have hf := folded_at_29 W hd h.transport x.1 (h.build w) B τ tr tr'
        (by simpa [treeBase, h0, h1] using he)
      simp only [h0, h1, if_false, hf]

/-- Retain tape decoding and opening data; construct the leaves, commitment
grammar and order. Message-locality evidence is still required in W. -/
def prover (enc : LeafEncoding K) {h : HonestProver K} {B : PackBasis F}
    {outputs : Statement K CommitHandle → R0Z.HonestView.Challenges K → Aux}
    {x : Statement K CommitHandle} (W : R1PhaseWire h B outputs x)
    (data : R1ProverP K CommitHandle Aux F W.toWire) : R1PhaseProver h B outputs x W where
  data := { data with leafVal := leafVal enc B }
  leaf_local := fun w τ tr tr' T u he =>
    leaf_local enc B h w x τ W.toWire W.decode_local tr tr' T u he

theorem constructed_causal (enc : LeafEncoding K) {h : HonestProver K} {B : PackBasis F}
    {outputs : Statement K CommitHandle → R0Z.HonestView.Challenges K → Aux}
    {x : Statement K CommitHandle} (W : R1PhaseWire h B outputs x)
    (data : R1ProverP K CommitHandle Aux F W.toWire) (w : h.Instance) :
    R1Z.CouplingR1PBin.RCausal W.toWire (prover enc W data).toProver h B outputs x w :=
  phase_causal W (prover enc W data) w

#print axioms leafVal
#print axioms leaf_local
#print axioms prover
#print axioms constructed_causal
end R1Z.PhaseLeafConstructionBin
