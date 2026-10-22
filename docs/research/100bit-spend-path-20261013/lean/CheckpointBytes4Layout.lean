import CheckpointBytes4SectionContents
import CheckpointBytes4RawFields

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes4Layout
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes4Ops CheckpointBytes4RawFields CheckpointBytes4ReaderFields
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep OraclePortCompactDraft
open MultiproofConeCanonical OraclePortCheckpointAbiC5

def KAt (ck : Slice U8) (offset : Nat) (q : CheckpointBytes4Sections.K) : Prop :=
  ∃ x, ExactLeafFieldCodec.decodeQM31 (slice (bytesOf ck.val) offset 16) = some x ∧ sourceK x = q

def EAt (ck : Slice U8) (offset : Nat) (q : aspis_core.field.wide_exact.WideExact) : Prop :=
  ∃ x, FoldedLeafCodec.decodeWide (slice (bytesOf ck.val) offset 32) = some x ∧ sourceE x = q

structure FlatFields (reserved : Bool) (ck : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (f : OraclePortCkptAbiSourceFields.Fields (ops reserved) ck .S2 p a) : Prop where
  stateBytes : p.state.val = (ck.val.drop 80).take 32
  root0Bytes : f.root0.val = (ck.val.drop 112).take 32
  root1Bytes : f.root1.val = (ck.val.drop 144).take 32
  gamma : EAt ck 176 p.gamma
  kappa : EAt ck 208 p.kappa
  alpha0 : EAt ck 240 f.alpha0
  alpha1 : EAt ck 272 f.alpha1
  rho : KAt ck 304 p.rho
  rhoCursor : f.rRho.at.val = 320
  rhoBacking : f.rRho.bytes = ck
  queryCursor : f.rQueries.at.val = 408
  semantic : ∃ model : Fin 10 → OraclePortCheckpointAbiC5.K,
    decodeKs 10 (slice (bytesOf ck.val) 408 160) = some model ∧
      p.semantic_alpha.val = (List.ofFn model).map sourceK
  semanticCursor : f.semanticEnd.val = 568
  x0 : KAt ck 568 f.x0
  y0 : KAt ck 584 f.y0
  x1 : KAt ck 600 f.x1
  y1 : KAt ck 616 f.y1
  claim : EAt ck 632 p.claim
  rhs : EAt ck 664 a.rhs
  power : KAt ck 696 a.power
  powerCursor : f.rPower.at.val = 712
  allocatedLength : f.allocated.val.length = 64
  weights : ∃ model : Fin 64 → OraclePortCheckpointAbiC5.K,
    decodeKs 64 (slice (bytesOf ck.val) 712 1024) = some model ∧
      a.weights.val = (List.ofFn model).map sourceK
  finalCursor : f.finalAt.val = 1736

/-- Full emitted cursor composition derives the semantic and weight bounds,
starting at 80 in an arbitrary successful 1768-byte S2 checkpoint. No field
canonicality or section-output equality is supplied as a hypothesis. -/
theorem flat_fields (reserved : Bool) (ck : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (f : OraclePortCkptAbiSourceFields.Fields (ops reserved) ck .S2 p a)
    (length : ck.val.length = 1768) : FlatFields reserved ck p a f := by
  obtain ⟨bytesState,cState,bState⟩ := raw_success 32#usize ⟨ck,80#usize⟩ f.rState p.state
    (by change 80+32 ≤ ck.val.length; omega) f.stateRead
  change f.rState.at.val = 112 at cState
  change f.rState.bytes = ck at bState
  change p.state.val = (ck.val.drop 80).take 32 at bytesState
  change f.rState.at.val = 112 at cState
  change p.state.val = (ck.val.drop 80).take 32 at bytesState
  obtain ⟨bytesRoot0,cRoot0,bRoot0⟩ := raw_success 32#usize f.rState f.rRoot0 f.root0
    (by rw [bState,cState]; change 112+32 ≤ ck.val.length; omega) f.root0Read
  rw [bState,cState] at bytesRoot0
  rw [cState] at cRoot0
  rw [bState] at bRoot0
  change f.rRoot0.at.val = 144 at cRoot0
  change f.root0.val = (ck.val.drop 112).take 32 at bytesRoot0
  obtain ⟨bytesRoot1,cRoot1,bRoot1⟩ := raw_success 32#usize f.rRoot0 f.rRoot1 f.root1
    (by rw [bRoot0,cRoot0]; change 144+32 ≤ ck.val.length; omega) f.root1Read
  rw [bRoot0,cRoot0] at bytesRoot1
  rw [cRoot0] at cRoot1
  rw [bRoot0] at bRoot1
  change f.rRoot1.at.val = 176 at cRoot1
  change f.root1.val = (ck.val.drop 144).take 32 at bytesRoot1
  obtain ⟨vGamma,dGamma,vGammaEq,cGamma,bGamma⟩ := e_success f.rRoot1 f.rGamma p.gamma
    (by rw [bRoot1,cRoot1]; omega) f.gammaRead
  rw [bRoot1,cRoot1] at dGamma
  rw [cRoot1] at cGamma
  rw [bRoot1] at bGamma
  obtain ⟨vKappa,dKappa,vKappaEq,cKappa,bKappa⟩ := e_success f.rGamma f.rKappa p.kappa
    (by rw [bGamma,cGamma]; omega) f.kappaRead
  rw [bGamma,cGamma] at dKappa
  rw [cGamma] at cKappa
  rw [bGamma] at bKappa
  obtain ⟨vAlpha0,dAlpha0,vAlpha0Eq,cAlpha0,bAlpha0⟩ := e_success f.rKappa f.rAlpha0 f.alpha0
    (by rw [bKappa,cKappa]; omega) f.alpha0Read
  rw [bKappa,cKappa] at dAlpha0
  rw [cKappa] at cAlpha0
  rw [bKappa] at bAlpha0
  obtain ⟨vAlpha1,dAlpha1,vAlpha1Eq,cAlpha1,bAlpha1⟩ := e_success f.rAlpha0 f.rAlpha1 f.alpha1
    (by rw [bAlpha0,cAlpha0]; omega) f.alpha1Read
  rw [bAlpha0,cAlpha0] at dAlpha1
  rw [cAlpha0] at cAlpha1
  rw [bAlpha0] at bAlpha1
  obtain ⟨vRho,dRho,vRhoEq,cRho,bRho⟩ := k_success f.rAlpha1 f.rRho p.rho
    (by rw [bAlpha1,cAlpha1]; omega) f.rhoRead
  rw [bAlpha1,cAlpha1] at dRho
  rw [cAlpha1] at cRho
  rw [bAlpha1] at bRho
  have queryLength : p.queries.val.length = 22 := p.queries.property
  obtain ⟨cQueries,bQueries⟩ := query_cursor reserved f.rRho f.rQueries p.queries.val f.queriesRead
    (by rw [bRho,cRho,queryLength]; omega)
  rw [queryLength,cRho] at cQueries
  rw [bRho] at bQueries
  obtain ⟨semantic,dSemantic,vSemantic,cSemantic⟩ := CheckpointBytes4SectionContents.semantic_contents
    ck f.rQueries.at f.semanticEnd p.semantic_alpha (by rw [cQueries]; omega) f.semanticRead
  rw [cQueries] at dSemantic cSemantic
  obtain ⟨vX0,dX0,vX0Eq,cX0,bX0⟩ := k_success ({f.rQueries with «at» := f.semanticEnd}) f.rX0 f.x0
    (by change f.semanticEnd.val+16 ≤ f.rQueries.bytes.val.length; rw [bQueries,cSemantic]; omega) f.x0Read
  change ExactLeafFieldCodec.decodeQM31 (slice (bytesOf f.rQueries.bytes.val) f.semanticEnd.val 16) = _ at dX0
  rw [bQueries,cSemantic] at dX0
  change f.rX0.at.val = f.semanticEnd.val+16 at cX0
  rw [cSemantic] at cX0
  change f.rX0.bytes = f.rQueries.bytes at bX0
  rw [bQueries] at bX0
  obtain ⟨vY0,dY0,vY0Eq,cY0,bY0⟩ := k_success (f.rX0) f.rY0 f.y0
    (by rw [bX0,cX0]; omega) f.y0Read
  rw [bX0,cX0] at dY0
  rw [cX0] at cY0
  rw [bX0] at bY0
  obtain ⟨vX1,dX1,vX1Eq,cX1,bX1⟩ := k_success (f.rY0) f.rX1 f.x1
    (by rw [bY0,cY0]; omega) f.x1Read
  rw [bY0,cY0] at dX1
  rw [cY0] at cX1
  rw [bY0] at bX1
  obtain ⟨vY1,dY1,vY1Eq,cY1,bY1⟩ := k_success (f.rX1) f.rY1 f.y1
    (by rw [bX1,cX1]; omega) f.y1Read
  rw [bX1,cX1] at dY1
  rw [cX1] at cY1
  rw [bX1] at bY1
  obtain ⟨vClaim,dClaim,vClaimEq,cClaim,bClaim⟩ := e_success (f.rY1) f.rClaim p.claim
    (by rw [bY1,cY1]; omega) f.claimRead
  rw [bY1,cY1] at dClaim
  rw [cY1] at cClaim
  rw [bY1] at bClaim
  obtain ⟨vRhs,dRhs,vRhsEq,cRhs,bRhs⟩ := e_success (f.rClaim) f.rRhs a.rhs
    (by rw [bClaim,cClaim]; omega) f.rhsRead
  rw [bClaim,cClaim] at dRhs
  rw [cClaim] at cRhs
  rw [bClaim] at bRhs
  obtain ⟨vPower,dPower,vPowerEq,cPower,bPower⟩ := k_success (f.rRhs) f.rPower a.power
    (by rw [bRhs,cRhs]; omega) f.powerRead
  rw [bRhs,cRhs] at dPower
  rw [cRhs] at cPower
  rw [bRhs] at bPower
  have lengthValue : f.finalLength = 64#usize := by
    exact (Result.ok.inj f.lengthCall).symm
  have allocated := (CheckpointBytes3Allocation.filled_success_content reserved f.finalLength f.zero
    f.allocated f.allocation).2
  have allocatedLength : f.allocated.val.length = 64 := by
    rw [allocated,List.length_replicate,lengthValue]
    rfl
  obtain ⟨weights,dWeights,vWeights,cWeights⟩ := CheckpointBytes4SectionContents.weights_contents
    ck f.rPower.at f.finalAt f.allocated a.weights
    (by rw [cPower,allocatedLength]; omega) f.weightsRead
  have weightPackage : ∃ model : Fin f.allocated.val.length → OraclePortCheckpointAbiC5.K,
      decodeKs f.allocated.val.length
        (slice (bytesOf ck.val) f.rPower.at.val (f.allocated.val.length*16)) = some model ∧
      a.weights.val = (List.ofFn model).map sourceK := ⟨weights,dWeights,vWeights⟩
  rw [cPower,allocatedLength] at weightPackage cWeights
  refine {
    stateBytes := bytesState, root0Bytes := bytesRoot0, root1Bytes := bytesRoot1,
    gamma := ⟨vGamma,dGamma,vGammaEq⟩, kappa := ⟨vKappa,dKappa,vKappaEq⟩,
    alpha0 := ⟨vAlpha0,dAlpha0,vAlpha0Eq⟩, alpha1 := ⟨vAlpha1,dAlpha1,vAlpha1Eq⟩,
    rho := ⟨vRho,dRho,vRhoEq⟩, rhoCursor := cRho, rhoBacking := bRho, queryCursor := cQueries,
    semantic := ⟨semantic,dSemantic,vSemantic⟩, semanticCursor := cSemantic,
    x0 := ⟨vX0,dX0,vX0Eq⟩, y0 := ⟨vY0,dY0,vY0Eq⟩,
    x1 := ⟨vX1,dX1,vX1Eq⟩, y1 := ⟨vY1,dY1,vY1Eq⟩,
    claim := ⟨vClaim,dClaim,vClaimEq⟩, rhs := ⟨vRhs,dRhs,vRhsEq⟩,
    power := ⟨vPower,dPower,vPowerEq⟩, powerCursor := cPower,
    allocatedLength := allocatedLength, weights := weightPackage, finalCursor := cWeights }

#print axioms flat_fields
end AspisR1.CheckpointBytes4Layout
end
