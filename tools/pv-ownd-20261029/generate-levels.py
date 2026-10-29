"""Small full-Link source cells; no byte-heap/recurrence normalization."""
from pathlib import Path
import argparse
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
def link(k,p,c):return f'⟨{k},{p},{c}⟩'
outputs={}
for phase,count in [('Private',21),('Append',20)]:
 for n in range(count):
  if phase=='Private':
   aux=864+(n//4)*16+1+2*(n%4)
   vals=[link(f'.privatePathCurrent {n}',(3+n)*16+11,aux),link(f'.privatePathLeft {n}',aux+1,(4+n)*16+12),link(f'.privatePathRight {n}',aux+1,(4+n)*16)]
   definition='privateLevel';extra=f'theorem base : pathBase {n}=some {aux} := rfl\n#print axioms base\n'
  else:
   vals=[link(f'.appendCurrentLeft {n}',(33+n)*16+11,(34+n)*16+12),link(f'.appendCurrentRight {n}',(33+n)*16+11,(34+n)*16)]
   definition='appendLevel';extra=''
  name=f'PV_OWND_{phase}{n:02d}'
  text=f'''import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.{name}
open PV_OWN_Link PV_OWND_LegacySource
/-- One bounded source iteration, with all kind payloads retained. -/
def values : List Link := [{','.join(vals)}]
theorem source : {definition} {n}=values := rfl
{extra}theorem count : values.length={len(vals)} := rfl
#print axioms source
#print axioms count
end R1Z.{name}
'''
  outputs[L/(name+'.lean')]=text
for path,text in outputs.items():
 if a.check:assert path.read_text()==text,path
 else:path.write_text(text)
print('checked' if a.check else 'generated',len(outputs),'isolated small source cells')
