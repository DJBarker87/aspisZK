import FJk_CopyWeightValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CopyStep
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
def row (pv pw cv cw : Array field.QM31 2#usize) : R0P.CopyRowExtension K :=
  ⟨decoded pv,decoded pw,decoded cv,decoded cw⟩
def step (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (index : Nat) (v : R0P.Variant)
    (r : R0P.CopyRowExtension K) (l : R0P.CopyLink) : R0P.CopyRowExtension K :=
  let w := R0P.copyLinkWeight l index v
  let p := R0P.copyAccumulateEndpoint r.producerValues r.producerWeights l.producer l.tag w patterns s
  let c := R0P.copyAccumulateEndpoint r.consumerValues r.consumerWeights l.consumer l.tag w patterns s
  ⟨p.1,p.2,c.1,c.2⟩
/-- Two actual endpoint calls on the SAME native link, weight and parsed operands. -/
theorem value (pv pw cv cw pv' pw' cv' cw' : Array field.QM31 2#usize)
    (l : CompiledPoolV1PairForestLink) (index : U64) (v : PoolV1PairForestCompiledVariantV1)
    (patterns : Array field.QM31 14#usize) (s : Selectors) (weight : U32)
    (hpv : canonical pv) (hpw : canonical pw) (hcv : canonical cv) (hcw : canonical cw)
    (hp : canonical patterns) (hh : canonical s.high) (hl : canonical s.low)
    (hg : JGa_LinkBounds.Good l) (rwgt : link_weight l index v=ok weight)
    (rp : accumulate_endpoint pv pw l.producer l.tag weight patterns s=ok (pv',pw'))
    (rc : accumulate_endpoint cv cw l.consumer l.tag weight patterns s=ok (cv',cw')) :
    canonical pv' ∧ canonical pw' ∧ canonical cv' ∧ canonical cw' ∧
    row pv' pw' cv' cw'=step (FIw_CopyEndpoint.modelSelectors s) (decoded patterns) index.val
      (FJk_CopyDescriptor.variant v) (row pv pw cv cw) (FJk_CopyDescriptor.link l) := by
  have weightV := FJk_CopyWeightValue.value (K:=K) l index v weight hg rwgt
  have p := FIw_CopyEndpoint.value pv pw pv' pw' l.producer l.tag weight patterns s
    hpv hpw hp hh hl hg.1.1 hg.1.2.1 hg.1.2.2 hg.2.2.1 rp
  have c := FIw_CopyEndpoint.value cv cw cv' cw' l.consumer l.tag weight patterns s
    hcv hcw hp hh hl hg.2.1.1 hg.2.1.2.1 hg.2.1.2.2 hg.2.2.1 rc
  refine ⟨p.1,p.2.1,c.1,c.2.1,?_⟩
  have pe := p.2.2
  have ce := c.2.2
  rw [←FJk_CopyDescriptor.endpoint_exact l.producer hg.1.1 hg.1.2.1 hg.1.2.2] at pe
  rw [←FJk_CopyDescriptor.endpoint_exact l.consumer hg.2.1.1 hg.2.1.2.1 hg.2.1.2.2] at ce
  rw [weightV.1] at pe ce
  have pairs := congrArg₂ (fun (p c : (Fin 2 → K) × (Fin 2 → K))=>
    (⟨p.1,p.2,c.1,c.2⟩ : R0P.CopyRowExtension K)) pe ce
  simpa only [row,step,FJk_CopyDescriptor.link] using pairs
#print axioms value
end AspisR1.FJk_CopyStep
end
