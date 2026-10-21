import OraclePortCkptAbiSourceFields

/-! Backing-slice provenance through the complete successful emitted reader.
Atomic reader preservation contracts stay explicit, not a whole-resume law. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.OraclePortCkptAbiSourceBacking
open AspisR1Stage2 OraclePortCkptAbiSourceFields

structure PreservesBacking (ops : ResumeOps) : Prop where
  raw : ∀ n r b out, ops.raw n r = ok (b,out) → out.bytes = r.bytes
  readE : ∀ r x out, ops.readE r = ok (.Ok x,out) → out.bytes = r.bytes
  readK : ∀ r x out, ops.readK r = ok (.Ok x,out) → out.bytes = r.bytes

theorem query_backing (ops : ResumeOps) (preserves : PreservesBacking ops)
    (r out : verifier.Reader) (qs : List U32) (reads : QueryReads ops r qs out) :
    out.bytes = r.bytes := by
  induction reads with
  | nil => rfl
  | cons read _ _ ih => exact ih.trans (preserves.raw _ _ _ _ read)

/-- All state, root, challenge, query, coordinate and accumulator read cursors
retain the same checkpoint. Semantic-alpha and weights explicitly receive ck
in Fields itself. This theorem does not infer account-snapshot provenance. -/
theorem all_fields_same_backing (ops : ResumeOps) (preserves : PreservesBacking ops)
    (ck : Slice U8) (v : transport.Variant) (p : verifier.Prepared) (a : verifier.Accumulator)
    (f : Fields ops ck v p a) :
    ([f.rState,f.rRoot0,f.rRoot1,f.rGamma,f.rKappa,f.rAlpha0,f.rAlpha1,
      f.rRho,f.rQueries,f.rX0,f.rY0,f.rX1,f.rY1,f.rClaim,f.rRhs,f.rPower].map
        (fun r => r.bytes)) = List.replicate 16 ck := by
  have bState : f.rState.bytes = ck := preserves.raw _ _ _ _ f.stateRead
  have bRoot0 := (preserves.raw _ _ _ _ f.root0Read).trans bState
  have bRoot1 := (preserves.raw _ _ _ _ f.root1Read).trans bRoot0
  have bGamma := (preserves.readE _ _ _ f.gammaRead).trans bRoot1
  have bKappa := (preserves.readE _ _ _ f.kappaRead).trans bGamma
  have bAlpha0 := (preserves.readE _ _ _ f.alpha0Read).trans bKappa
  have bAlpha1 := (preserves.readE _ _ _ f.alpha1Read).trans bAlpha0
  have bRho := (preserves.readK _ _ _ f.rhoRead).trans bAlpha1
  have bQueries := (query_backing ops preserves _ _ _ f.queriesRead).trans bRho
  have bX0 : f.rX0.bytes = ck := (preserves.readK _ _ _ f.x0Read).trans bQueries
  have bY0 := (preserves.readK _ _ _ f.y0Read).trans bX0
  have bX1 := (preserves.readK _ _ _ f.x1Read).trans bY0
  have bY1 := (preserves.readK _ _ _ f.y1Read).trans bX1
  have bClaim := (preserves.readE _ _ _ f.claimRead).trans bY1
  have bRhs := (preserves.readE _ _ _ f.rhsRead).trans bClaim
  have bPower := (preserves.readK _ _ _ f.powerRead).trans bRhs
  simp only [List.map_cons,List.map_nil,bState,bRoot0,bRoot1,bGamma,bKappa,bAlpha0,
    bAlpha1,bRho,bQueries,bX0,bY0,bX1,bY1,bClaim,bRhs,bPower]
  rfl

#print axioms query_backing
#print axioms all_fields_same_backing
end AspisR1.OraclePortCkptAbiSourceBacking
