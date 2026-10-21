"""Generate bounded explicit success inversion, never a concrete recurrence."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
base=root/'docs/research/100bit-spend-path-20261013/lean'
orig=(base/'OraclePortCkptAbiSource.lean').read_text()
prefix=orig[orig.index('  unfold verifier.resumeWithOps at success'):orig.index('  obtain ⟨first, firstCall, h⟩')]
prefix=prefix.replace('resume_bind_success','bind_success')
helpers=orig[orig.index('private theorem checkpoint_guard'):orig.index('structure Entry')]
s='''import OraclePortCkptAbiTry

/-! Complete successful emitted resume: every Prepared/Accumulator output is
bound to the exact read call which produced it. No arithmetic/codec law is
assumed. Identifying those calls with C5 is a separate atomic codec join. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.OraclePortCkptAbiSourceFields
open AspisR1Stage2 OraclePortCkptAbiTry

'''+helpers+'''inductive QueryReads (ops : ResumeOps) :
    verifier.Reader → List U32 → verifier.Reader → Prop where
  | nil (r : verifier.Reader) : QueryReads ops r [] r
  | cons {r r1 r2 : verifier.Reader} {b : Array U8 4#usize} {q : U32} {qs : List U32}
      (read : ops.raw 4#usize r = ok (b,r1))
      (decode : lift (core.num.U32.from_le_bytes b) = ok q)
      (tail : QueryReads ops r1 qs r2) : QueryReads ops r (q::qs) r2

structure Fields (ops : ResumeOps) (ck : Slice U8)
    (v : transport.Variant) (p : verifier.Prepared) (a : verifier.Accumulator) where
  variant : p.variant = v
  root0 : Array U8 32#usize
  root1 : Array U8 32#usize
  roots : p.roots = Array.make 2#usize [root0,root1]
  rState : verifier.Reader
  rRoot0 : verifier.Reader
  rRoot1 : verifier.Reader
  stateRead : ops.raw 32#usize ⟨ck,80#usize⟩ = ok (p.state,rState)
  root0Read : ops.raw 32#usize rState = ok (root0,rRoot0)
  root1Read : ops.raw 32#usize rRoot0 = ok (root1,rRoot1)
  rGamma : verifier.Reader
  rKappa : verifier.Reader
  alpha0 : aspis_core.field.wide_exact.WideExact
  alpha1 : aspis_core.field.wide_exact.WideExact
  rAlpha0 : verifier.Reader
  rAlpha1 : verifier.Reader
  alpha : p.alpha = Array.make 2#usize [alpha0,alpha1]
  gammaRead : ops.readE rRoot1 = ok (.Ok p.gamma,rGamma)
  kappaRead : ops.readE rGamma = ok (.Ok p.kappa,rKappa)
  alpha0Read : ops.readE rKappa = ok (.Ok alpha0,rAlpha0)
  alpha1Read : ops.readE rAlpha0 = ok (.Ok alpha1,rAlpha1)
  rRho : verifier.Reader
  rhoRead : ops.readK rAlpha1 = ok (.Ok p.rho,rRho)
  rQueries : verifier.Reader
  queriesRead : QueryReads ops rRho p.queries.val rQueries
  validate : ops.validate p.queries = ok (.Ok ())
  semanticEnd : Usize
  semanticRead : ops.readSemanticAlpha ck rQueries.at = ok (.Ok (p.semantic_alpha,semanticEnd))
  x0 : aspis_core.field.QM31
  y0 : aspis_core.field.QM31
  x1 : aspis_core.field.QM31
  y1 : aspis_core.field.QM31
  coordinates : p.z = Array.make 2#usize [⟨x0,y0⟩,⟨x1,y1⟩]
  rX0 : verifier.Reader
  rY0 : verifier.Reader
  rX1 : verifier.Reader
  rY1 : verifier.Reader
  x0Read : ops.readK {rQueries with «at» := semanticEnd} = ok (.Ok x0,rX0)
  y0Read : ops.readK rX0 = ok (.Ok y0,rY0)
  x1Read : ops.readK rY0 = ok (.Ok x1,rX1)
  y1Read : ops.readK rX1 = ok (.Ok y1,rY1)
  rClaim : verifier.Reader
  rRhs : verifier.Reader
  rPower : verifier.Reader
  claimRead : ops.readE rY1 = ok (.Ok p.claim,rClaim)
  rhsRead : ops.readE rClaim = ok (.Ok a.rhs,rRhs)
  powerRead : ops.readK rRhs = ok (.Ok a.power,rPower)
  finalLength : Usize
  zero : aspis_core.field.QM31
  allocated : alloc.vec.Vec aspis_core.field.QM31
  finalAt : Usize
  checksumEnd : Usize
  lengthCall : ops.finalLen v = ok finalLength
  zeroCall : ops.zeroK = ok zero
  allocation : ops.filled finalLength zero = ok (.Ok allocated)
  weightsRead : ops.readWeights ck rPower.at allocated = ok (.Ok (a.weights,finalAt))
  checksumEndCall : Slice.len ck - 32#usize = ok checksumEnd
  cursor : finalAt = checksumEnd
  nextByte : U8
  nextRead : Slice.index_usize ck 9#usize = ok nextByte
  nextCast : lift (UScalar.cast .Usize nextByte) = ok a.next

/-- Full output provenance for the emitted decoder, on every successful run.
The proof only inverts executed binds/guards; it does not unfold byte codecs. -/
theorem successful_fields (ops : ResumeOps) {H : Type}
    (digestInst : aspis_core.digest.Digest32 H)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (success : verifier.resumeWithOps ops digestInst bytes proof public1 v hash =
      ok (.Ok (p,acc))) : Nonempty (Fields ops bytes v p acc) := by
'''+prefix
s+='''  obtain ⟨⟨state,rState⟩,stateRead,h⟩ := bind_success _ _ _ h
  obtain ⟨⟨root0,rRoot0⟩,root0Read,h⟩ := bind_success _ _ _ h
  obtain ⟨⟨root1,rRoot1⟩,root1Read,h⟩ := bind_success _ _ _ h
'''
prev='rRoot1'
for val,r in [('gamma','rGamma'),('kappa','rKappa'),('alpha0','rAlpha0'),('alpha1','rAlpha1'),('rho','rRho')]:
 s+=f'  try dsimp only at h\n  obtain ⟨{val},{r},{val}Read,h⟩ := read_success (ops.{'readK' if val == 'rho' else 'readE'} {prev}) _ (p,acc) h\n'
 prev=r
for i in range(22):
 s+=f'  obtain ⟨⟨qb{i},rq{i}⟩,qr{i},h⟩ := bind_success _ _ _ h\n'
 s+=f'  obtain ⟨q{i},qd{i},h⟩ := bind_success _ _ _ h\n'
s+='''  obtain ⟨validated,validate,h⟩ := bind_success _ _ _ h
  obtain ⟨unit,valid,h⟩ := try_success _ _ _ h
  cases unit
  subst validated
  obtain ⟨semanticResult,semanticCall,h⟩ := bind_success _ _ _ h
  obtain ⟨⟨semanticAlpha,semanticEnd⟩,semanticEq,h⟩ := try_success _ _ _ h
  subst semanticResult
'''
prev='{rq21 with «at» := semanticEnd}'
for val,r in [('x0','rX0'),('y0','rY0'),('x1','rX1'),('y1','rY1'),('claim','rClaim'),('rhs','rRhs'),('power','rPower')]:
 kind='readE' if val in ['claim','rhs'] else 'readK'
 s+=f'  try dsimp only at h\n  obtain ⟨{val},{r},{val}Read,h⟩ := read_success (ops.{kind} {prev}) _ (p,acc) h\n'
 prev=r
s+='''  obtain ⟨finalLength,lengthCall,h⟩ := bind_success _ _ _ h
  obtain ⟨zero,zeroCall,h⟩ := bind_success _ _ _ h
  obtain ⟨allocatedResult,allocatedCall,h⟩ := bind_success _ _ _ h
  obtain ⟨allocated,allocatedEq,h⟩ := try_success _ _ _ h
  subst allocatedResult
  obtain ⟨weightsResult,weightsCall,h⟩ := bind_success _ _ _ h
  obtain ⟨⟨weights,finalAt⟩,weightsEq,h⟩ := try_success _ _ _ h
  subst weightsResult
  obtain ⟨cursor,h⟩ := checkpoint_guard _ _ _ h
  have cursorEq : finalAt = end1 := by simpa only [bne_eq_false_iff_eq] using cursor
  obtain ⟨next,nextCast,h⟩ := bind_success _ _ _ h
  have finalEq := core.result.Result.Ok.inj (Result.ok.inj h)
  have preparedEq := congrArg Prod.fst finalEq
  have accumulatorEq := congrArg Prod.snd finalEq
  dsimp only at preparedEq accumulatorEq
  subst p acc
  refine ⟨{
    variant := rfl, root0 := root0, root1 := root1, roots := rfl,
    rState := rState, rRoot0 := rRoot0, rRoot1 := rRoot1,
    stateRead := stateRead, root0Read := root0Read, root1Read := root1Read,
    rGamma := rGamma, rKappa := rKappa, alpha0 := alpha0, alpha1 := alpha1,
    rAlpha0 := rAlpha0, rAlpha1 := rAlpha1, alpha := rfl,
    gammaRead := gammaRead, kappaRead := kappaRead,
    alpha0Read := alpha0Read, alpha1Read := alpha1Read,
    rRho := rRho, rhoRead := rhoRead, rQueries := rq21, queriesRead := ?_,
    validate := validate, semanticEnd := semanticEnd, semanticRead := semanticCall,
    x0 := x0, y0 := y0, x1 := x1, y1 := y1, coordinates := rfl,
    rX0 := rX0, rY0 := rY0, rX1 := rX1, rY1 := rY1,
    x0Read := x0Read, y0Read := y0Read, x1Read := x1Read, y1Read := y1Read,
    rClaim := rClaim, rRhs := rRhs, rPower := rPower,
    claimRead := claimRead, rhsRead := rhsRead, powerRead := powerRead,
    finalLength := finalLength, zero := zero, allocated := allocated,
    finalAt := finalAt, checksumEnd := end1, lengthCall := lengthCall,
    zeroCall := zeroCall, allocation := allocatedCall, weightsRead := weightsCall,
    checksumEndCall := hend, cursor := cursorEq, nextByte := nextByte,
    nextRead := nextByteRead, nextCast := nextCast }⟩
'''
# Prefix originally discards the next-byte call; preserve it.
s=s.replace('obtain ⟨nextByte, _, h⟩','obtain ⟨nextByte, nextByteRead, h⟩')
chain='(QueryReads.nil _)'
for i in reversed(range(22)):
 chain=f'(QueryReads.cons qr{i} qd{i} {chain})'
s+=f'  exact {chain}\n'
s+='''
#print axioms checkpoint_guard
#print axioms checkpoint_guard_prop
#print axioms successful_fields
end AspisR1.OraclePortCkptAbiSourceFields
'''
(base/'OraclePortCkptAbiSourceFields.lean').write_text(s)
