from pathlib import Path
import json
E=Path(__file__).resolve().parent;G=E/'NLV_generated';sites=json.loads((E/'NLV_SITES.json').read_text())
s=''.join('import NLV_Step_'+n+'\nimport NLV_Frame_'+n+'\n' for n in sites)
s+='''set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem source_step (cfg : Configuration) (s : NLJ_Tx1.State) :
 CheckpointBytes5Effect.bind (step cfg s) (continuation cfg)=denote cfg s := by
 cases s with
 | mk i l =>
   cases l with
'''
for n,d in sites.items():s+='   | '+n+(' '+d['args'] if d['args'] else '')+' => exact step_'+n+' cfg i'+(' '+d['args'] if d['args'] else '')+'\n'
for goal,post in [('frame','FramePost'),('progress','ProgressPost')]:
 s+='theorem source_'+goal+' (cfg : Configuration) (s : NLJ_Tx1.State) :\n AllLeaves ('+post+' s) (step cfg s) := by\n cases s with\n | mk i l =>\n   cases l with\n'
 for n,d in sites.items():s+='   | '+n+(' '+d['args'] if d['args'] else '')+' => exact '+goal+'_'+n+' cfg i'+(' '+d['args'] if d['args'] else '')+'\n'
s+='''theorem decrease (cfg : Configuration)
 (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (s after : NLJ_Tx1.State)
 (before log : SdkC_Source.Log)
 (returned : SdkC_Source.run h (step cfg s) before=(ok (.inr after),log)) :
 rank after<rank s := leaves_run (ProgressPost s) h (step cfg s) (source_progress cfg s) _ before log returned
theorem input_frame (cfg : Configuration)
 (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (s after : NLJ_Tx1.State)
 (before log : SdkC_Source.Log)
 (returned : SdkC_Source.run h (step cfg s) before=(ok (.inr after),log)) :
 after.input=s.input := leaves_run (FramePost s) h (step cfg s) (source_frame cfg s) _ before log returned
theorem positive (s : NLJ_Tx1.State) : 0<rank s := by
 cases s with | mk i l => cases l <;> decide
#print axioms source_step
#print axioms source_frame
#print axioms source_progress
#print axioms decrease
#print axioms input_frame
#print axioms positive
end AspisR1.NLV_Tree
end
''';(G/'NLV_All.lean').write_text(s)
