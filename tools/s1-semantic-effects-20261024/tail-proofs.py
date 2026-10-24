#!/usr/bin/env python3
from pathlib import Path
import sys
S=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
rows=[('RoundStep','roundStep','RoundModel.step','(B : RoundModel.Boundaries)','(prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)\n    (alpha : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Usize)','B D prefix1 transcript alpha running round',['SemanticValidatedExact'],['semanticValidated_erasure']),('Rounds','rounds','RoundModel.rounds','(B : RoundModel.Boundaries)','(prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)','B D prefix1 transcript',['RoundStepExact'],['roundStep_erasure']),('CircleValidated','circleValidated','FinishModel.circle_validated','(B : FinishModel.Boundaries)','(self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord)','B D self record1',['SampleBlockExact'],['sampleBlock_erasure']),('Finish','finish','FinishModel.finish','(R : RoundModel.Boundaries) (B : FinishModel.Boundaries)','(pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)\n    (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)\n    (obs : Option (verifier.Phase → Result Unit))','R B D pub prefix1 transcript challenges obs',['RoundsExact','CircleValidatedExact'],['rounds_erasure','circleValidated_erasure'])]
for stem,name,old,extra,params,args,deps,lemmas in rows:
 out=f'import S1SemanticCode{stem}V1\n'+''.join('import S1SemanticCode'+d+'V1\n' for d in deps)+'''set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

'''+f'''/-- Complete original source outcome, including early rejection and outer failure. -/
theorem {name}_erasure {extra} {{H : Type}} (D : aspis_core.Digest32 H)
    {params} :
    erase ({name} {args})={old} {args} := by
  unfold {name} {old}
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | simp_all)
'''+''.join('    | (solve | apply '+l+')\n' for l in lemmas)+'''    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift]'''+''.join(' | rw ['+l+']' for l in lemmas)+'''
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

#print axioms '''+name+'''_erasure
end AspisR1PublicPreparation.S1SemanticCode
'''
 if stem!='CircleValidated':out=out.replace('    | (solve | simp_all)\n','')
 p=S/('S1SemanticCode'+stem+'ExactV1.lean')
 if '--check' in sys.argv:assert p.read_text()==out
 else:p.write_text(out)
