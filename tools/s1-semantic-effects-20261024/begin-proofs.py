#!/usr/bin/env python3
from pathlib import Path
import sys
S=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
head='''import S1SemanticCodeBeginV1
import S1SemanticCodeSemanticValidatedExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

'''
result=head
for row in [13,9,5,0]:
 name='begin'+(str(row) if row else '')
 if row:
  params=f'''(prefix1 : r1_wire.Prefix) (transcript{row} : r1_wire.SemanticTranscript H)
    (val val1 val2 val{row-1} : aspis_core.field.QM31)
    (index_mut_back{row-4} : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize)'''
  args=f'prefix1 transcript{row} val val1 val2 val{row-1} index_mut_back{row-4}'
 else:params='(prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)';args='prefix1 transcript'
 nextlemma={13:'',9:' | rw [begin13_erasure]',5:' | rw [begin9_erasure]',0:' | rw [begin5_erasure]'}[row]
 helpers='\n'.join('    | (solve | apply begin'+str(n)+'_erasure_native)' for n in [13,9,5] if n>row and (row==0 or n==row+4))
 result+=f'''theorem {name}_erasure_native {{H : Type}} (D : aspis_core.Digest32 H)
    {params} :
    erase ({name} D {args})={name}_native D {args} := by
  unfold {name} {name}_native
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | rfl)
{helpers}
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [semanticValidated_erasure]'''+nextlemma.replace('_erasure]','_erasure_native]')+'''
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

'''
result+='''/-- Fission is definitionally the same retained source body. All captures,
rejections and current transcript values are retained without a success premise. -/
theorem begin_native_eq {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    begin_native D prefix1 transcript=r1_wire.begin D prefix1 transcript := by
  unfold begin_native begin5_native begin9_native begin13_native r1_wire.begin
  rfl

theorem begin_erasure {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    erase (begin D prefix1 transcript)=r1_wire.begin D prefix1 transcript := by
  rw [begin_erasure_native,begin_native_eq]

#print axioms begin_native_eq
#print axioms begin_erasure
end AspisR1PublicPreparation.S1SemanticCode
'''
p=S/'S1SemanticCodeBeginExactV1.lean'
if '--check' in sys.argv:assert p.read_text()==result
else:p.write_text(result)
