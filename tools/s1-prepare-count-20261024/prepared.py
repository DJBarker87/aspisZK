#!/usr/bin/env python3
from pathlib import Path
import runpy,sys
R=Path(__file__).resolve().parents[2]
S=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
base='''import S1PrepareBudgetTacticV1
import S1PreparedCompleteHashErasureV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedBudget
open Aeneas Aeneas.Std Result
open PreparedHashCode
attribute [local irreducible] PreparedHashCode.effects
'''
rows=[
('new',1,'','(hash : H) (state : Array U8 32#usize) (variant : transport.Variant)','hash state variant','PreparedHashEffects.new',[]),
('absorb',1,'','(self : transcript.Transcript H) (row : U8) (payload : Slice U8)','self row payload','PreparedHashEffects.absorb',[]),
('block',3,'','(self : transcript.Transcript H) (row : U8) (payload : Slice U8)','self row payload','PreparedHashEffects.block',['absorb']),
('scalar',3,'(B : PreparedModel.Boundaries)','(self : transcript.Transcript H) (row : U8) (payload : Slice U8) (nonzero : Bool)','self row payload nonzero','PreparedScalarEffects.scalar',['block']),
('scalar_k',3,'(B : PreparedModel.Boundaries)','(self : transcript.Transcript H) (row : U8) (payload : Slice U8)','self row payload','PreparedScalarEffects.scalar_k',['block']),
('queries',17,'(Q : QueriesModel.Boundaries)','(self : transcript.Transcript H) (row : U8) (payload : Slice U8)','self row payload','PreparedQueryEffects.queries',['absorb']),
('preparation',33,'(B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries)','(sem : r1_semantic.Verified H) (view : verifier.View) (hash : H) (scratch : Array aspis_core.field.WideExact 29#usize)','sem view hash scratch','PreparedSourceEffects.prepare',['new','scalar','scalar_k','queries'])]
byname={r[0]:r for r in rows}
def tactic(deps):
 s="  repeat' first\n    | (solve | apply pure_bound)\n    | (solve | apply lift_bound)\n"
 for d in deps:
  cost=byname[d][1];fn=byname[d][5]
  s+=f'''    | (apply mono (n:={cost}) <;> first | omega | (solve | apply {d}_bounded))
    | (budget_then_for {cost} {fn}
       <;> first | omega | (solve | apply {d}_bounded) | intro x)
'''
 s+='''    | (apply lift_bind;intro x)
    | (budget_then 1 <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split
'''
 return s
out=base
for name,cap,extra,params,args,fn,deps in rows:
 effect='(preparationEffects B Q)' if name=='preparation' else 'effects B' if name in ['scalar','scalar_k'] else 'effects Q' if name=='queries' else 'effects'
 out+=f'''\n/-- Counts every materialized digest on every response path, with rejection prefixes. -/
theorem {name}_bounded {extra} {{H : Type}} (D : aspis_core.Digest32 H)
    {params} : bounded {cap} ({fn} {effect} D {args}) := by
  unfold {fn}'''+(' preparationEffects' if name=='preparation' else '')+'\n'+tactic(deps)+'\nattribute [local irreducible] '+fn+'\n'
out+='\n'+'\n'.join('#print axioms '+r[0]+'_bounded' for r in rows)+'\nend AspisR1PublicPreparation.PreparedBudget\n'
p=S/'S1PreparedBudgetV1.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
