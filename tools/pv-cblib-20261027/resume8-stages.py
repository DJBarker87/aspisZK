"""Generate small symbolic SHA stages; never normalize arithmetic state.
Each step has one named four-round application and (from round16) one
named schedule application. --check compares the emitted source bytes.
"""
from pathlib import Path
import sys
root=Path(__file__).resolve().parents[2];b=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
header='''open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockStage{n:02}
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
set_option autoImplicit false
'''
# The final stage is the independently verified extracted feed-forward.
s='''import R1Z.PV_CBL_FallbackFeedForward
import R1Z.PV_CBL_FallbackRoundsModel
'''+header.format(n=16)+'''
def source (original : Array U32 8#usize) (abef cdgh : A4)
    (_w0 _w1 _w2 _w3 : A4) : Result (Array U32 8#usize) :=
  PV_CBL_FallbackFeedForward.source original abef cdgh
def value (original current : State) (_w0 _w1 _w2 _w3 : A4) : State :=
  PV_CBL_FallbackFeedForward.value original current
theorem shape (original current : State) (w0 w1 w2 w3 : A4) :
    source (PV_CBL_FallbackStateCodec.encode original)
      (pack current.a current.b current.e current.f) (pack current.c current.d current.g current.h)
      w0 w1 w2 w3 = ok (PV_CBL_FallbackStateCodec.encode (value original current w0 w1 w2 w3)) :=
  PV_CBL_FallbackFeedForward.shape original current
#print axioms source
#print axioms value
#print axioms shape
end R1Z.PV_CBL_BlockStage16
'''
outputs={'PV_CBL_BlockStage16.lean':s}
for i in reversed(range(16)):
 nxt=f'PV_CBL_BlockStage{i+1:02}';q=f'PV_CBL_FallbackConstantMatrix.q{i}'
 imp=f'import R1Z.PV_CBL_BlockValueBoundary\nimport R1Z.{nxt}\nimport R1Z.PV_CBL_BlockFourValue\nimport R1Z.PV_CBL_BlockScheduleValue\nimport R1Z.PV_CBL_FallbackConstantMatrix\n'
 s=imp+header.format(n=i)
 # Keep the original four words throughout the first four groups; thereafter
 # the register ring is the last sixteen scalar schedule words.
 rest=f'w{i}' if i<4 else 'w'
 ss='' if i<4 else '  let w ← PV_CBL_FallbackBlock.sha_fallback_reference.schedule w0 w1 w2 w3\n'
 vv='' if i<4 else '  let w := PV_CBL_BlockValueBoundary.schedule w0 w1 w2 w3\n'
 ring='w0 w1 w2 w3' if i<4 else 'w1 w2 w3 w'
 proof_schedule='' if i<4 else '  rw [PV_CBL_BlockValueBoundary.schedule_source]\n  simp only [bind_tc_ok]\n  generalize hw : PV_CBL_BlockValueBoundary.schedule w0 w1 w2 w3 = word\n'
 proof_rest=f'w{i}' if i<4 else 'word'
 proof_ring='w0 w1 w2 w3' if i<4 else 'w1 w2 w3 word'
 s+=f'''def source (original : Array U32 8#usize) (abef cdgh : A4)
    (w0 w1 w2 w3 : A4) : Result (Array U32 8#usize) := do
{ss}  let (a,c) ← PV_CBL_FallbackFourModel.source abef cdgh {rest} {q}
  {nxt}.source original a c {ring}
def value (original current : State) (w0 w1 w2 w3 : A4) : State :=
{vv}  let current := PV_CBL_BlockValueBoundary.four current {rest} {q}
  {nxt}.value original current {ring}
theorem shape (original current : State) (w0 w1 w2 w3 : A4) :
    source (PV_CBL_FallbackStateCodec.encode original)
      (pack current.a current.b current.e current.f) (pack current.c current.d current.g current.h)
      w0 w1 w2 w3 = ok (PV_CBL_FallbackStateCodec.encode (value original current w0 w1 w2 w3)) := by
  unfold source value
{proof_schedule}  rw [PV_CBL_BlockValueBoundary.four_source]
  rw [PV_CBL_BlockValueBoundary.packed_bind]
  exact {nxt}.shape original (PV_CBL_BlockValueBoundary.four current {proof_rest} {q}) {proof_ring}
#print axioms source
#print axioms value
#print axioms shape
end R1Z.PV_CBL_BlockStage{i:02}
'''
 outputs[f'PV_CBL_BlockStage{i:02}.lean']=s
for name,s in outputs.items():
 p=b/name
 if '--check' in sys.argv:assert p.read_text()==s,name
 else:p.write_text(s)
print('stages',len(outputs),'check' if '--check' in sys.argv else 'emit')
