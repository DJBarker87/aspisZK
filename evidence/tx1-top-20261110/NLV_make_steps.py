from pathlib import Path
import json
E=Path(__file__).resolve().parent;G=E/'NLV_generated';sites=json.loads((E/'NLV_SITES.json').read_text())
(G/'NLV_Continuation.lean').write_text('''import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result NLJ_Tx1
open CheckpointBytes5Effect (Code)
def continuation (cfg : Configuration) : Post → Code Out
 | .inl out => pure out
 | .inr after => denote cfg after
end AspisR1.NLV_Tree
end
''')
for name,d in sites.items():
 local='.'+name+(' '+d['args'] if d['args'] else '')
 s='''import NLV_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem step_'''+name+' (cfg : Configuration) (i : Input) '+d['params']+''' :
 CheckpointBytes5Effect.bind (step cfg ⟨i,'''+local+'''⟩) (continuation cfg) =
 denote cfg ⟨i,'''+local+'''⟩ := by
 dsimp only [step,advance,denote,suffix_'''+name+''',nextOrError,continuation]
 simp only [Bind.bind,Pure.pure,NLV_Algebra.assoc,CheckpointBytes5Effect.bind]
 all_goals repeat' first
 | rfl
 | (apply NLV_Algebra.same; intro reply; cases reply)
 | (split <;> simp only [Bind.bind,Pure.pure,CheckpointBytes5Effect.bind])
#print axioms step_'''+name+'''
end AspisR1.NLV_Tree
end
'''
 (G/('NLV_Step_'+name+'.lean')).write_text(s)
