from pathlib import Path
import json
E=Path(__file__).resolve().parent;G=E/'NLV_generated';sites=json.loads((E/'NLV_SITES.json').read_text())
for name,d in sites.items():
 local='.'+name+(' '+d['args'] if d['args'] else '')
 s='''import NLV_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
'''
 for goal,post in [('frame','FramePost'),('progress','ProgressPost')]:
  s+='theorem '+goal+'_'+name+' (cfg : Configuration) (i : Input) '+d['params']+''' :
 AllLeaves ('''+post+' ⟨i,'+local+'⟩) (step cfg ⟨i,'+local+'''⟩) := by
 dsimp only [step]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | (apply leaves_bind; intro reply; cases reply)
 | (split)
 | (simp only [AllLeaves,'''+post+''',advance,rank,nextOrError])
 | trivial
 | decide
#print axioms '''+goal+'_'+name+'\n'
 s+='end AspisR1.NLV_Tree\nend\n';(G/('NLV_Frame_'+name+'.lean')).write_text(s)

# Final authoritative frame bundle: NLV_generated/NLV_Frames.lean.
# Historical separate-file templates were unvalidated and are not regenerated in the final gate.
