#!/usr/bin/env python3
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];S=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
rows=[('SemanticValidated','semanticValidated','r1_wire.SemanticTranscript.semantic_validated','(self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord)','self record1','sampleBlock_erasure','SampleBlockExact'),('Begin','begin','r1_wire.begin','(prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)','prefix1 transcript','semanticValidated_erasure','SemanticValidatedExact'),('NewTranscript','newTranscript','r1_wire.SemanticTranscript.new','(hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize)','hash publicBytes root','','SampleBlockExact'),('PublicTranscript','publicTranscript','r1_semantic.public_transcript','(pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize)','pub hash root','newTranscript_erasure','NewTranscriptExact')]
for stem,name,old,params,args,lemma,dep in rows:
 if name=="begin":continue
 target='S1SemanticCode'+stem+'ExactV1'
 out=f'''import S1SemanticCode{stem}V1
import S1SemanticCode{dep}V1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {{A B : Type}} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Exact complete source return, with errors and outer fail/div retained. -/
theorem {name}_erasure {{H : Type}} (D : aspis_core.Digest32 H)
    {params} :
    erase ({name} D {args})={old} D {args} := by
  unfold {name} {old}
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [erase_digest]'''+(' | rw ['+lemma+']' if lemma else '')+'''
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

#print axioms '''+name+'''_erasure
end AspisR1PublicPreparation.S1SemanticCode
'''
 p=S/(target+'.lean')
 if '--check' in sys.argv:assert p.read_text()==out
 else:p.write_text(out)
