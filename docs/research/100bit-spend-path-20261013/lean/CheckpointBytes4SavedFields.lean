import CheckpointBytes4Layout
import CheckpointBytes4QueryDecode
import CheckpointBytes4FixedWidth

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes4SavedFields
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes4Ops CheckpointBytes4Layout CheckpointBytes4ReaderFields
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep OraclePortCompactDraft
open MultiproofConeCanonical OraclePortCheckpointAbiC5 OraclePortCheckpointSlicesC5
open CheckpointBytes4FixedWidth

structure BodyMatches (p : verifier.Prepared) (a : verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared) (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K E) : Prop where
  variant : p.variant = .S2
  state : bytesOf p.state.val = bytes pm.state
  roots : p.roots.val.map (fun b => bytesOf b.val) = [bytes (pm.roots 0),bytes (pm.roots 1)]
  gamma : p.gamma = sourceE pm.gamma
  kappa : p.kappa = sourceE pm.kappa
  alpha : p.alpha.val = [sourceE (pm.alpha 0),sourceE (pm.alpha 1)]
  rho : p.rho = sourceK pm.rho
  queries : p.queries.val.map UScalar.val = List.ofFn (fun j => (pm.queries j).val)
  semantic : p.semantic_alpha.val = (List.ofFn pm.semanticAlpha).map sourceK
  coordinates : p.z.val.flatMap (fun z => [z.x,z.y]) = (List.ofFn pm.coordinates).map sourceK
  claim : p.claim = sourceE pm.claim
  rhs : a.rhs = sourceE am.rhs
  power : a.power = sourceK am.power
  weights : a.weights.val = (List.ofFn am.weights).map sourceK

private theorem e_value (ck : Slice U8) (offset : Nat) (q : aspis_core.field.wide_exact.WideExact)
    (x : E) (field : EAt ck offset q)
    (decoded : FoldedLeafCodec.decodeWide (slice (bytesOf ck.val) offset 32) = some x) :
    q = sourceE x := by
  obtain ⟨y,run,value⟩ := field
  have same : x = y := Option.some.inj (decoded.symm.trans run)
  exact value.symm.trans (congrArg sourceE same.symm)

private theorem k_value (ck : Slice U8) (offset : Nat) (q : CheckpointBytes4Sections.K)
    (x : OraclePortCheckpointAbiC5.K) (field : KAt ck offset q)
    (decoded : ExactLeafFieldCodec.decodeQM31 (slice (bytesOf ck.val) offset 16) = some x) :
    q = sourceK x := by
  obtain ⟨y,run,value⟩ := field
  have same : x = y := Option.some.inj (decoded.symm.trans run)
  exact value.symm.trans (congrArg sourceK same.symm)

private theorem query_value (b : Bytes) (q : Fin 262144)
    (success : OraclePortCheckpointPreparedC5.decodeQuery b = some q) : little b = q.val := by
  unfold OraclePortCheckpointPreparedC5.decodeQuery at success
  split at success
  · have eq := Option.some.inj success
    exact congrArg Fin.val eq
  · cases success

/-- Authentic saved bytes identify every returned body field. This consumes
concrete callback Fields and kernel section refinements, not a whole-output
or observation-equality hypothesis. next is handled by the saved header. -/
theorem body_matches (reserved : Bool) (ck : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (f : OraclePortCkptAbiSourceFields.Fields (ops reserved) ck .S2 p a)
    (H : Bytes → State) (stored pub : Bytes) (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K E)
    (encoding : bytesOf ck.val = encode H stored pub pm am) : BodyMatches p a pm am := by
  have length : ck.val.length = 1768 := by
    have h := congrArg List.length encoding
    simpa only [bytesOf,List.length_map,encode_length] using h
  have flat := flat_fields reserved ck p a f length
  obtain ⟨_,_,_,state,root0,root1,gamma,kappa,alpha0,alpha1⟩ := prefix_slices H stored pub pm am
  obtain ⟨rho,queries,semantic,coordinates,claim⟩ := prepared_slices H stored pub pm am
  obtain ⟨rhs,power,weights⟩ := accumulator_decodes H stored pub pm am
  have stateValue : bytesOf p.state.val = bytes pm.state := by
    have h := congrArg bytesOf flat.stateBytes
    simp only [bytesOf,List.map_drop,List.map_take] at h
    change bytesOf p.state.val = slice (bytesOf ck.val) 80 32 at h
    rw [encoding,state] at h
    exact h
  have root0Value : bytesOf f.root0.val = bytes (pm.roots 0) := by
    have h := congrArg bytesOf flat.root0Bytes
    simp only [bytesOf,List.map_drop,List.map_take] at h
    change bytesOf f.root0.val = slice (bytesOf ck.val) 112 32 at h
    rw [encoding,root0] at h
    exact h
  have root1Value : bytesOf f.root1.val = bytes (pm.roots 1) := by
    have h := congrArg bytesOf flat.root1Bytes
    simp only [bytesOf,List.map_drop,List.map_take] at h
    change bytesOf f.root1.val = slice (bytesOf ck.val) 144 32 at h
    rw [encoding,root1] at h
    exact h
  have vGamma : p.gamma = sourceE pm.gamma := e_value ck 176 p.gamma pm.gamma flat.gamma
    (by rw [encoding,gamma,encodeE,FoldedLeafCodec.decodeWide_encode])
  have vKappa : p.kappa = sourceE pm.kappa := e_value ck 208 p.kappa pm.kappa flat.kappa
    (by rw [encoding,kappa,encodeE,FoldedLeafCodec.decodeWide_encode])
  have vAlpha0 : f.alpha0 = sourceE (pm.alpha 0) := e_value ck 240 f.alpha0 (pm.alpha 0) flat.alpha0
    (by rw [encoding,alpha0,encodeE,FoldedLeafCodec.decodeWide_encode])
  have vAlpha1 : f.alpha1 = sourceE (pm.alpha 1) := e_value ck 272 f.alpha1 (pm.alpha 1) flat.alpha1
    (by rw [encoding,alpha1,encodeE,FoldedLeafCodec.decodeWide_encode])
  have vClaim : p.claim = sourceE pm.claim := e_value ck 632 p.claim pm.claim flat.claim
    (by rw [encoding,claim,encodeE,FoldedLeafCodec.decodeWide_encode])
  have vRho : p.rho = sourceK pm.rho := k_value ck 304 p.rho pm.rho flat.rho
    (by rw [encoding,rho,encodeK,ExactLeafFieldCodec.decodeQM31_encodeQM31])
  have vRhs : a.rhs = sourceE am.rhs := e_value ck 664 a.rhs am.rhs flat.rhs
    (by rw [encoding]; exact rhs)
  have vPower : a.power = sourceK am.power := k_value ck 696 a.power am.power flat.power
    (by rw [encoding]; exact power)
  have vSemantic : p.semantic_alpha.val = (List.ofFn pm.semanticAlpha).map sourceK := by
    obtain ⟨model,run,contents⟩ := flat.semantic
    rw [encoding,semantic,decodeKs_encode] at run
    have same := Option.some.inj run
    simpa only [← same] using contents
  have vWeights : a.weights.val = (List.ofFn am.weights).map sourceK := by
    obtain ⟨model,run,contents⟩ := flat.weights
    rw [encoding,weights] at run
    have same := Option.some.inj run
    simpa only [← same] using contents
  have coordRun : decodeKs 4 (slice (bytesOf ck.val) 568 64) = some pm.coordinates := by
    rw [encoding,coordinates,decodeKs_encode]
  have coordinateAt (j : Fin 4) : ExactLeafFieldCodec.decodeQM31
      (slice (bytesOf ck.val) (568+j.val*16) 16) = some (pm.coordinates j) := by
    have h := decode_at ExactLeafFieldCodec.decodeQM31 16 4
      (slice (bytesOf ck.val) 568 64) pm.coordinates coordRun j
    simpa only [slice,slice_slice _ 568 64 (j.val*16) 16 (by have := j.isLt; omega)] using h
  have vx0 := k_value ck 568 f.x0 (pm.coordinates 0) flat.x0 (by simpa using coordinateAt 0)
  have vy0 := k_value ck 584 f.y0 (pm.coordinates 1) flat.y0 (by simpa using coordinateAt 1)
  have vx1 := k_value ck 600 f.x1 (pm.coordinates 2) flat.x1 (by simpa using coordinateAt 2)
  have vy1 := k_value ck 616 f.y1 (pm.coordinates 3) flat.y1 (by simpa using coordinateAt 3)
  have queryRun : OraclePortCheckpointPreparedC5.decodeQueries (slice (bytesOf ck.val) 320 88) =
      some pm.queries := by
    rw [encoding,queries,OraclePortCheckpointPreparedC5.decodeQueries_encode]
  have queryAt (j : Fin 22) : little (slice (bytesOf ck.val) (320+j.val*4) 4) = (pm.queries j).val := by
    have h := decode_at OraclePortCheckpointPreparedC5.decodeQuery 4 22
      (slice (bytesOf ck.val) 320 88) pm.queries queryRun j
    have h' : OraclePortCheckpointPreparedC5.decodeQuery
        (slice (bytesOf ck.val) (320+j.val*4) 4) = some (pm.queries j) := by
      simpa only [slice,slice_slice _ 320 88 (j.val*4) 4 (by have := j.isLt; omega)] using h
    exact query_value _ _ h'
  have queryLength : p.queries.val.length = 22 := p.queries.property
  have vQueries : p.queries.val.map UScalar.val = List.ofFn (fun j => (pm.queries j).val) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_ofFn,queryLength]
    · intro j hj hk
      have bound : j < 22 := by simpa only [List.length_ofFn] using hk
      have read := CheckpointBytes4QueryDecode.query_values reserved f.rRho f.rQueries p.queries.val f.queriesRead
        (by rw [flat.rhoCursor,flat.rhoBacking,queryLength]; omega)
        ⟨j,by simpa only [queryLength] using bound⟩
      rw [flat.rhoCursor,flat.rhoBacking] at read
      simp only [List.getElem_map,List.getElem_ofFn]
      exact read.symm.trans (queryAt ⟨j,bound⟩)
  refine {
    variant := f.variant, state := stateValue, roots := ?_, gamma := vGamma, kappa := vKappa,
    alpha := ?_, rho := vRho, queries := vQueries, semantic := vSemantic,
    coordinates := ?_, claim := vClaim, rhs := vRhs, power := vPower, weights := vWeights }
  · rw [f.roots]
    change [bytesOf f.root0.val,bytesOf f.root1.val] = _
    rw [root0Value,root1Value]
  · rw [f.alpha]
    change [f.alpha0,f.alpha1] = _
    rw [vAlpha0,vAlpha1]
  · rw [f.coordinates]
    change [f.x0,f.y0,f.x1,f.y1] = _
    rw [vx0,vy0,vx1,vy1]
    simp only [List.ofFn_succ,List.ofFn_zero,List.map_cons,List.map_nil]
    rfl

#print axioms e_value
#print axioms k_value
#print axioms query_value
#print axioms body_matches
end AspisR1.CheckpointBytes4SavedFields
end
