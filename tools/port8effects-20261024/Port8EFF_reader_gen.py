import sys
def emit(path, content):
 if "--check" in sys.argv:
  assert path.read_text()==content,str(path)
 else:path.write_text(content)
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'CheckpointBytes5Resume.lean').read_text().split('def program ',1)[1].split('\nprivate theorem',1)[0]
assert s.count('liftResult (i7 - 32#usize)')==1
s=s.replace('liftResult (i7 - 32#usize)','liftResult (lift (Std.Usize.wrapping_sub i7 32#usize))')
s=s.replace('liftResult (tail ops','liftResult (Port4A_NativeReader.tail ops')
out='''import Port4A_NativeReader
import Port4A_ReaderNormalize
set_option autoImplicit false
namespace AspisR1.Port8EFF_NativeReader
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
-- Current emitted parent: wrapping subtraction and current native decoder tail.
def program '''+s+'''
private theorem if_tail {A : Type} (p : Prop) [Decidable p] (a b c : A)
    (h : b=c) : (if p then a else b)=(if p then a else c) := by rw [h]

theorem source (ops : ResumeOps) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (bytes proof pub : Slice U8) (v : transport.Variant) (hash : Hash) :
    erase D hash (program ops bytes proof pub v)=
      Port4A_NativeReader.resume ops D bytes proof pub v hash := by
  simp only [program,erase_bind,erase_lift,erase_read,erase_pure,erase_ite]
  unfold Port4A_NativeReader.resume
  repeat
    first
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value success
    | apply if_tail
  rfl

#print axioms if_tail
#print axioms source
end AspisR1.Port8EFF_NativeReader
'''
emit(L/'Port8EFF_NativeReader.lean',out)
