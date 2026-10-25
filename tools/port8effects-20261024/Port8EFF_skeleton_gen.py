import sys
def emit(path, content):
 if "--check" in sys.argv:
  assert path.read_text()==content,str(path)
 else:path.write_text(content)
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'Port8EFF_NativeReader.lean').read_text().split('def program ',1)[1].split('\nprivate theorem',1)[0]
s=s.replace('(v : transport.Variant) : Code','(v : transport.Variant) (endResult : Result Usize) (tailFn : U8 → Usize → Slice U8 → Digest → Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)) : Code').replace('lift (Std.Usize.wrapping_sub i7 32#usize)','endResult').replace('Port4A_NativeReader.tail ops bytes v','tailFn')
header='''import Port8EFF_Bodies
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port8EFF_ReaderSkeleton
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
-- Same emitted parent, with just its pure subtraction Result exposed.
def skeleton '''
footer='''
theorem native (ops : ResumeOps) (ck proof pub : Slice U8) (v : transport.Variant) :
    Port8EFF_NativeReader.program ops ck proof pub v=
      skeleton ops ck proof pub v (lift (Usize.wrapping_sub (Slice.len ck) 32#usize)) (Port4A_NativeReader.tail ops ck v) := rfl

theorem retained (ops : ResumeOps) (ck proof pub : Slice U8) (v : transport.Variant) :
    CheckpointBytes5Resume.program ops ck proof pub v=
      skeleton ops ck proof pub v (Slice.len ck-32#usize) (CheckpointBytes5Resume.tail ops ck v) := rfl

#print axioms native
#print axioms retained
end AspisR1.Port8EFF_ReaderSkeleton
end
'''
sig=s[:s.index(' := do')]
body=s.split('  else\n',1)[1]
body='\n'.join(line[2:] if line.startswith('  ') else line for line in body.splitlines())
after=header.replace('def skeleton ','def afterSize ')+sig+' := do\n'+body
skeleton="""
def skeleton (ops : ResumeOps) (bytes proof public1 : Slice U8) (v : transport.Variant)
    (endResult : Result Usize)
    (tailFn : U8 → Usize → Slice U8 → Digest → Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)) :
    Code (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) :=
  .step (ops.checkpointSize v) fun i1 =>
    if Slice.len bytes != i1 then .done (.Err .Checkpoint)
    else afterSize ops bytes proof public1 v endResult tailFn
"""
emit(L/'Port8EFF_ReaderSkeleton.lean',after+skeleton+footer)
