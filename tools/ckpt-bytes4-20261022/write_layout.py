from pathlib import Path
s='''import CheckpointBytes4SectionContents
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
'''
prevR='⟨ck,80#usize⟩'; prevC=None; prevB=None
for name,field,offset in [('State','p.state',80),('Root0','f.root0',112),('Root1','f.root1',144)]:
 bound='by change 80+32 ≤ ck.val.length; omega' if name=='State' else f'by rw [b{prevC},c{prevC}]; change {offset}+32 ≤ ck.val.length; omega'
 s+=f'  obtain ⟨bytes{name},c{name},b{name}⟩ := raw_success 32#usize {prevR} f.r{name} {field}\n    ({bound}) f.{name[0].lower()+name[1:]}Read\n'
 if name=='State':s+='  change f.rState.at.val = 112 at cState\n  change f.rState.bytes = ck at bState\n  change p.state.val = (ck.val.drop 80).take 32 at bytesState\n'
 else:
  s+=f'  rw [b{prevC},c{prevC}] at bytes{name}\n  rw [c{prevC}] at c{name}\n  rw [b{prevC}] at b{name}\n'
 s+=f'  change f.r{name}.at.val = {offset+32} at c{name}\n  change {field}.val = (ck.val.drop {offset}).take 32 at bytes{name}\n'
 prevR='f.r'+name;prevC=name
# reader scalar chain
for kind,name,q,method in [('e','Gamma','p.gamma','gammaRead'),('e','Kappa','p.kappa','kappaRead'),('e','Alpha0','f.alpha0','alpha0Read'),('e','Alpha1','f.alpha1','alpha1Read'),('k','Rho','p.rho','rhoRead')]:
 s+=f'  obtain ⟨v{name},d{name},v{name}Eq,c{name},b{name}⟩ := {kind}_success {prevR} f.r{name} {q}\n    (by rw [b{prevC},c{prevC}]; omega) f.{method}\n'
 s+=f'  rw [b{prevC},c{prevC}] at d{name}\n  rw [c{prevC}] at c{name}\n  rw [b{prevC}] at b{name}\n'
 prevR='f.r'+name;prevC=name
s+='''  have queryLength : p.queries.val.length = 22 := p.queries.property
  obtain ⟨cQueries,bQueries⟩ := query_cursor reserved f.rRho f.rQueries p.queries.val f.queriesRead
    (by rw [bRho,cRho,queryLength]; omega)
  rw [queryLength,cRho] at cQueries
  rw [bRho] at bQueries
  obtain ⟨semantic,dSemantic,vSemantic,cSemantic⟩ := CheckpointBytes4SectionContents.semantic_contents
    ck f.rQueries.at f.semanticEnd p.semantic_alpha (by rw [cQueries]; omega) f.semanticRead
  rw [cQueries] at dSemantic cSemantic
'''
prevR='{f.rQueries with «at» := f.semanticEnd}';prevC='Semantic'
for kind,name,q,method in [('k','X0','f.x0','x0Read'),('k','Y0','f.y0','y0Read'),('k','X1','f.x1','x1Read'),('k','Y1','f.y1','y1Read'),('e','Claim','p.claim','claimRead'),('e','Rhs','a.rhs','rhsRead'),('k','Power','a.power','powerRead')]:
 if name=='X0':
  bound='by change f.semanticEnd.val+16 ≤ f.rQueries.bytes.val.length; rw [bQueries,cSemantic]; omega'
 else:bound=f'by rw [b{prevC},c{prevC}]; omega'
 s+=f'  obtain ⟨v{name},d{name},v{name}Eq,c{name},b{name}⟩ := {kind}_success ({prevR}) f.r{name} {q}\n    ({bound}) f.{method}\n'
 if name=='X0':
  s+='  change ExactLeafFieldCodec.decodeQM31 (slice (bytesOf f.rQueries.bytes.val) f.semanticEnd.val 16) = _ at dX0\n  rw [bQueries,cSemantic] at dX0\n  change f.rX0.at.val = f.semanticEnd.val+16 at cX0\n  rw [cSemantic] at cX0\n  change f.rX0.bytes = f.rQueries.bytes at bX0\n  rw [bQueries] at bX0\n'
 else:
  s+=f'  rw [b{prevC},c{prevC}] at d{name}\n  rw [c{prevC}] at c{name}\n  rw [b{prevC}] at b{name}\n'
 prevR='f.r'+name;prevC=name
s+='''  have lengthValue : f.finalLength = 64#usize := by
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
'''
# subst lengthValue is wrong (equality variable) handled via cast on weights after rewriting allocatedLength
s=s.replace('  subst lengthValue\n  exact ⟨weights,dWeights,vWeights⟩','  simpa only [allocatedLength] using (show ∃ model : Fin f.allocated.val.length → OraclePortCheckpointAbiC5.K,\n    decodeKs f.allocated.val.length (slice (bytesOf ck.val) 712 (f.allocated.val.length*16)) = some model ∧\n      a.weights.val = (List.ofFn model).map sourceK from ⟨weights,by simpa only [allocatedLength] using dWeights,vWeights⟩)')
Path('docs/research/100bit-spend-path-20261013/lean/CheckpointBytes4Layout.lean').write_text(s)
