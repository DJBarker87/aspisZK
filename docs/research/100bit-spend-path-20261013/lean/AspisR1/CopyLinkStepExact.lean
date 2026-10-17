import CopyLinkWeightExact

/-! One literal Copy link body, composing source weight and both endpoints.
The following step is the exact monadic fragment in the sealed source loop;
the enclosing registry read, increment and recursive continuation remain separate. -/
set_option autoImplicit false
namespace AspisR1.CopyLinkStepExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CopyLinkWeightExact AspisR1.CopyEndpointExact
open AspisR1.ArrayUpdateCanonicalExact
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev QM := field.QM31
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

def runStep (link : Raw) (index : U64) (variant : Variant)
    (patterns : Array QM 14#usize) (selectors : Selectors)
    (pv pw cv cw : Array QM 2#usize) :
    Result (Array QM 2#usize × Array QM 2#usize × Array QM 2#usize × Array QM 2#usize) := do
  let weight ← weightFn link index variant
  let (pv1,pw1) ←
    AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.accumulate_endpoint
      pv pw link.producer link.tag weight patterns selectors
  let (cv1,cw1) ←
    AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.accumulate_endpoint
      cv cw link.consumer link.tag weight patterns selectors
  ok (pv1,pw1,cv1,cw1)

def modelRow (pv pw cv cw : Array QM 2#usize) : R0P.CopyRowExtension ExactQM :=
  ⟨decodedCells pv, decodedCells pw, decodedCells cv, decodedCells cw⟩

def modelStep (row : R0P.CopyRowExtension ExactQM) (link : R0P.CopyLink)
    (index : Nat) (variant : R0P.Variant)
    (patterns : Fin 14 → ExactQM) (selectors : R0P.CopySelectors ExactQM) :
    R0P.CopyRowExtension ExactQM :=
  let weight := R0P.copyLinkWeight link index variant
  let producer := R0P.copyAccumulateEndpoint row.producerValues row.producerWeights
    link.producer link.tag weight patterns selectors
  let consumer := R0P.copyAccumulateEndpoint row.consumerValues row.consumerWeights
    link.consumer link.tag weight patterns selectors
  ⟨producer.1, producer.2, consumer.1, consumer.2⟩

theorem step_success (link : Raw) (index : U64) (variant : Variant)
    (patterns : Array QM 14#usize) (selectors : Selectors)
    (pv pw cv cw : Array QM 2#usize)
    (hkind : link.weight_kind.val < 5) (hlevel : link.weight_level.val < 64)
    (hb : EndpointBounds link) (htag : link.tag.val < AspisR1.TerminalLiftM31Exact.P)
    (hpatterns : CanonicalArray patterns)
    (hhigh : CanonicalArray selectors.high) (hlow : CanonicalArray selectors.low)
    (hpv : CanonicalArray pv) (hpw : CanonicalArray pw)
    (hcv : CanonicalArray cv) (hcw : CanonicalArray cw) :
    ∃ pv1 pw1 cv1 cw1,
      runStep link index variant patterns selectors pv pw cv cw = .ok (pv1,pw1,cv1,cw1) ∧
      CanonicalArray pv1 ∧ CanonicalArray pw1 ∧ CanonicalArray cv1 ∧ CanonicalArray cw1 ∧
      modelRow pv1 pw1 cv1 cw1 =
        modelStep (modelRow pv pw cv cw) (modelLink link hkind hb) index.val
          (modelVariant variant) (decodedCells patterns) (modelSelectors selectors) := by
  obtain ⟨weight, hw, hbit, hweight⟩ := link_weight_exact link index variant hkind hlevel hb
  obtain ⟨pv1, pw1, hprod, hcpv, hcpw, hvprod⟩ :=
    endpoint_success pv pw link.producer link.tag weight patterns selectors
      hpv hpw hpatterns hhigh hlow hb.producerRow hb.producerSlot hb.producerPattern htag
  obtain ⟨cv1, cw1, hcons, hccv, hccw, hvcons⟩ :=
    endpoint_success cv cw link.consumer link.tag weight patterns selectors
      hcv hcw hpatterns hhigh hlow hb.consumerRow hb.consumerSlot hb.consumerPattern htag
  rw [hweight] at hvprod hvcons
  refine ⟨pv1,pw1,cv1,cw1,?_,hcpv,hcpw,hccv,hccw,?_⟩
  · simp only [runStep, hw, hprod, hcons, bind_tc_ok]
    rfl
  · change modelRow pv1 pw1 cv1 cw1 =
      { producerValues := (R0P.copyAccumulateEndpoint (decodedCells pv) (decodedCells pw)
          (AspisR1.CopyEndpointExact.modelEndpoint link.producer hb.producerRow hb.producerSlot hb.producerPattern)
          link.tag.val (R0P.copyLinkWeight (modelLink link hkind hb) index.val (modelVariant variant))
          (decodedCells patterns) (modelSelectors selectors)).1,
        producerWeights := (R0P.copyAccumulateEndpoint (decodedCells pv) (decodedCells pw)
          (AspisR1.CopyEndpointExact.modelEndpoint link.producer hb.producerRow hb.producerSlot hb.producerPattern)
          link.tag.val (R0P.copyLinkWeight (modelLink link hkind hb) index.val (modelVariant variant))
          (decodedCells patterns) (modelSelectors selectors)).2,
        consumerValues := (R0P.copyAccumulateEndpoint (decodedCells cv) (decodedCells cw)
          (AspisR1.CopyEndpointExact.modelEndpoint link.consumer hb.consumerRow hb.consumerSlot hb.consumerPattern)
          link.tag.val (R0P.copyLinkWeight (modelLink link hkind hb) index.val (modelVariant variant))
          (decodedCells patterns) (modelSelectors selectors)).1,
        consumerWeights := (R0P.copyAccumulateEndpoint (decodedCells cv) (decodedCells cw)
          (AspisR1.CopyEndpointExact.modelEndpoint link.consumer hb.consumerRow hb.consumerSlot hb.consumerPattern)
          link.tag.val (R0P.copyLinkWeight (modelLink link hkind hb) index.val (modelVariant variant))
          (decodedCells patterns) (modelSelectors selectors)).2 }
    rw [←hvprod, ←hvcons]
    rfl

#print axioms step_success
end
end AspisR1.CopyLinkStepExact
