#!/usr/bin/env python3
from pathlib import Path
import runpy,sys
P=Path(__file__).resolve().parent;R=P.parents[1];S=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
rows=runpy.run_path(str(R/'tools/s1-semantic-effects-20261024/oracle-valid.py'))['rows']
caps={'sampleBlock':3,'semanticValidated':3,'begin13':6,'begin9':18,'begin5':30,'begin':45,'newTranscript':1,'publicTranscript':1,'roundStep':3,'rounds':30,'circleValidated':3,'finish':36,'verify':82}

def tactic(deps):
 text='''  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
'''
 for name in deps:
  cap=caps[name]
  text+=f'''    | (apply mono (n:={cap})
       <;> first | omega | (solve | apply {name}_bounded))
    | (budget_then_for {cap} {name}
       <;> first | omega | (solve | apply {name}_bounded) | intro x)
'''
 text+='''    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split
'''
 return text
out='''import S1PrepareBudgetTacticV1
import S1SemanticCodeVerifyExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode PreparedBudget
attribute [local irreducible] PreparedHashCode.effects

'''
for name,extra,params,args,deps in rows:
 lead='B ' if name in ['roundStep','rounds','circleValidated'] else 'R B ' if name=='finish' else '(finish R B) ' if name=='verify' else ''
 out+=f'''/-- Every source-code path, including rejection before the last read. -/
theorem {name}_bounded {extra} {{H : Type}} (D : aspis_core.Digest32 H)
    {params} : bounded {caps[name]} ({name} {lead}D {args}) := by
  unfold {name}
'''+tactic(deps)+'\nattribute [local irreducible] '+name+'\n\n'
out+='\n'.join('#print axioms '+r[0]+'_bounded' for r in rows)+'\nend AspisR1PublicPreparation.S1SemanticCode\n'
p=S/'S1SemanticBudgetV1.lean'
if __name__=='__main__':
 if '--check' in sys.argv:assert p.read_text()==out
 else:p.write_text(out)
