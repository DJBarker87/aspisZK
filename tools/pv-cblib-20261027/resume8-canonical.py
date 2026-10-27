from pathlib import Path
import sys
b=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
outputs={}
s='''import R1Z.PV_CBL_BlockStage16
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_CanonicalStage16
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
def value (original current : State) (_w0 _w1 _w2 _w3 : A4) : State :=
  PV_CBL_FallbackFeedForward.value original current
theorem source_value (original current : State) (w0 w1 w2 w3 : A4) :
    PV_CBL_BlockStage16.value original current w0 w1 w2 w3 = value original current w0 w1 w2 w3 := rfl
#print axioms value
#print axioms source_value
end R1Z.PV_CBL_CanonicalStage16
'''
outputs['PV_CBL_CanonicalStage16.lean']=s
for i in reversed(range(16)):
 n=f'PV_CBL_CanonicalStage{i:02}';nxt=f'PV_CBL_CanonicalStage{i+1:02}';src=f'PV_CBL_BlockStage{i:02}';q=f'PV_CBL_FallbackConstantMatrix.q{i}'
 w=f'w{i}' if i<4 else 'w';ring='w0 w1 w2 w3' if i<4 else 'w1 w2 w3 w'
 sched='' if i<4 else '  let w := PV_CBL_CanonicalBoundary.schedule w0 w1 w2 w3\n'
 s=f'''import R1Z.{nxt}
import R1Z.{src}
import R1Z.PV_CBL_CanonicalBoundary
open Aeneas Aeneas.Std Result
namespace R1Z.{n}
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
def value (original current : State) (w0 w1 w2 w3 : A4) : State :=
{sched}  let current := PV_CBL_CanonicalBoundary.four current {w} {q}
  {nxt}.value original current {ring}
theorem source_value (original current : State) (w0 w1 w2 w3 : A4) :
    {src}.value original current w0 w1 w2 w3 = value original current w0 w1 w2 w3 := by
  simp only [{src}.value,value,PV_CBL_CanonicalBoundary.four_eq,
    PV_CBL_CanonicalBoundary.schedule_eq,{nxt}.source_value]
#print axioms value
#print axioms source_value
end R1Z.{n}
'''
 outputs[n+'.lean']=s
for name,s in outputs.items():
 p=b/name
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('canonical stages',len(outputs))
