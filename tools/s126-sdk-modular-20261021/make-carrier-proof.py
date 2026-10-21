#!/usr/bin/env python3
"""Emit finite case analysis of the exact Prepared source sequence, no reduction loops."""
from pathlib import Path
P=Path(__file__).with_name('carrier-transport-proof.lean.inc')
N='[Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,if_true,if_false,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from]'
lines=[];counter=0
def put(i,s):lines.append(' '*i+s)
def norm(i,hyp=None):
 if hyp:put(i,'try simp only '+N+' at '+hyp)
 put(i,'try simp only '+('['+hyp+','+N[1:] if hyp else N))
def leaf(i):put(i,'simp only '+N+' <;> try rfl')
def step(i,expr,pat,cont):
 global counter
 counter+=1;hyp='h'+str(counter);put(i,f'cases {hyp} : {expr} with');put(i,'| fail e =>');norm(i+2,hyp);put(i+2,'try rfl');put(i,'| div =>');norm(i+2,hyp);put(i+2,'try rfl');put(i,'| ok '+('value' if pat.startswith('⟨') else pat)+' =>')
 if pat.startswith('⟨'):put(i+2,'rcases value with '+pat)
 norm(i+2,hyp);cont(i+2)
D='(retainedDigest D)';S='(retainedSem sem)'
def tail(i,double):
 t='t4' if double else 't3';qt='t5' if double else 't4';rt='t6' if double else 't5';row='31' if double else '30'
 def query_done(j):
  put(j,'cases queryResult with');put(j,'| Err e => simp only '+N+' <;> try rfl');put(j,'| Ok actualQueries =>');norm(j+2)
  step(j+2,f'({row}#u8 + 1#u8 : Result U8)','nextRow',lambda k:
   step(k,'lift (Array.to_slice (Std.Array.empty U8))','emptyBytes',lambda k:
    step(k,f'AspisR1PublicPreparation.PreparedModel.scalar_k B.sampling {D} {qt} nextRow emptyBytes',f'⟨rho,{rt}⟩',lambda k:
     step(k,'B.powers 29#usize gamma','scratchOld',lambda k:
      step(k,f'B.claim {D} {S} v.y1 (retainedE v.inactive) scratchOld kappa','claimResult',claim_done)))))
 def claim_done(j):
  put(j,'cases claimResult with');put(j,'| Err e => simp only '+N+' <;> try rfl');put(j,'| Ok actualClaim =>');leaf(j+2)
 step(i,f'B.sampling.queries {D} {t} {row}#u8 v.final_message',f'⟨queryResult,{qt}⟩',query_done)
def double(i):
 step(i,'(32#usize + 224#usize : Result Usize)','capacity',lambda j:
  step(j,'core.option.Option.unwrap v.folded_root','foldedRoot',lambda j:
   step(j,'lift (Array.to_slice foldedRoot)','foldedBytes',lambda j:
    step(j,'alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 capacity) foldedBytes','bytes1',lambda j:
     step(j,'alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 v.round1','bytes2',lambda j:
      step(j,f'AspisR1PublicPreparation.PreparedModel.scalar B.sampling {D} t3 30#u8 (alloc.vec.Vec.deref bytes2) false','⟨alpha1,t4⟩',lambda k:tail(k,True)))))))
def folds(i):
 def branches(j):
  put(j,'by_cases hdouble : foldCount=2#usize');put(j,'·');norm(j+2,'hdouble');double(j+2);put(j,'·');norm(j+2,'hdouble');tail(j+2,False)
 step(i,'AspisR1PublicPreparation.transport.Variant.folds (retainedVariant v.variant)','foldCount',branches)
put(2,'unfold prepare transported AspisR1PublicPreparation.OriginalPreparedNative.prepare');put(2,'simp only [semanticState,newT,scalar,toBytes,folds,queries,scalarK,powers,claim,zero,');put(4,'AspisR1PublicPreparation.OriginalPreparedNative.zero,retainedView]')
step(2,f'AspisR1PublicPreparation.r1_wire.SemanticTranscript.impl.state {D} {S}.transcript','seed',lambda i:
 step(i,f'AspisR1PublicPreparation.transcript.Transcript.new {D} hash seed (retainedVariant v.variant)','t',lambda i:
  step(i,f'AspisR1PublicPreparation.PreparedModel.scalar B.sampling {D} t 27#u8 v.y1 true','⟨gamma,t1⟩',lambda i:
   step(i,'B.sampling.toBytes (retainedE v.inactive)','encoded',lambda i:
    step(i,'lift (Array.to_slice encoded)','bytes',lambda i:
     step(i,f'AspisR1PublicPreparation.PreparedModel.scalar B.sampling {D} t1 28#u8 bytes false','⟨kappa,t2⟩',lambda i:
      step(i,f'AspisR1PublicPreparation.PreparedModel.scalar B.sampling {D} t2 29#u8 v.round0 false','⟨alpha0,t3⟩',folds)))))))
P.write_text('\n'.join(lines)+'\n');print('Emitted',counter,'named Result case splits across both source branches')
