from pathlib import Path
import json
E=Path(__file__).resolve().parent;G=E/'NLV_generated';sites=json.loads((E/'NLV_SITES.json').read_text());prior=[];parent='NLV_Emitted'
for name,d in reversed(list(sites.items())):
 args=(' '+d['args']) if d['args'] else ''
 s='import '+parent+'''\nimport NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_'''+name+' (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input) '+d['params']+''' (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_'''+name+' cfg i'+args+''') before =
 SdkC_Source.run h (NLV_Tree.suffix_'''+name+' cfg i'+args+''') before := by
 unfold NLV_Emitted.suffix_'''+name+' NLV_Tree.suffix_'+name+'''
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run'''+''.join(',eq_'+p for p in prior)+'''])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run'''+''.join(',eq_'+p for p in prior)+'''])
#print axioms eq_'''+name+'''
end AspisR1.NLV_EmitProof
end
'''
 (G/('NLV_Emit_'+name+'.lean')).write_text(s);prior.append(name);parent='NLV_Emit_'+name
