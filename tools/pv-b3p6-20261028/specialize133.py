"""Small fixed schedule certificates; no large recurrence or limit override."""
from pathlib import Path
import sys
D=Path('evidence/pv-b3p6-20261028/lean')
def lit(xs):return '['+', '.join(f'{"path" if k else "link"} {p} {c}' for k,p,c in xs)+']'
sponge=[(False,f*16+11,t*16) for f,t in [(1,2),(2,3),(25,26),(27,28),(28,29),(30,31),(31,32)]]
initial=[(False,*x) for x in [(11,28),(12,412),(44,428),(60,428)]]
private=[]
for l in range(21):
 a=864+l//4*16+1+2*(l%4);private += [(True,(3+l)*16+11,a),(True,a+1,(4+l)*16+12),(True,a+1,(4+l)*16)]
values=[(False,*x) for x in [(44,960),(460,962),(508,964),(960,966),(962,966),(964,967),(966,967),(64,969),(865,969),(523,970),(475,540),(523,540),(970,528)]]
append=[]
for l in range(20):append += [(False,(33+l)*16+11,(34+l)*16+12),(False,(33+l)*16+11,(34+l)*16)]
legacy=sponge+initial+private+values+append
parts=[('sponge','''([(1,2),(2,3),(25,26),(27,28),(28,29),(30,31),(31,32)] : List (Nat × Nat)).map
    (fun (f,t) => link (f*16+11) (t*16))''',sponge),('private','''(List.range 21).flatMap (fun level =>
    [path ((3+level)*16+11) (legacyAux level),
     path (legacyAux level+1) ((4+level)*16+12),
     path (legacyAux level+1) ((4+level)*16)])''',private),('append','''(List.range 20).flatMap (fun level =>
    [link ((33+level)*16+11) ((34+level)*16+12),
     link ((33+level)*16+11) ((34+level)*16)])''',append)]
s='import PV_B3P_Schedule133\nnamespace PV_B3P_LegacyValues133\nopen PV_B3P_Schedule133\nset_option autoImplicit false\n'
for name,expr,xs in parts:
 s+=f'def {name}Fixed : List Link := {lit(xs)}\ntheorem {name}_eval : {expr} = {name}Fixed := by rfl\n#print axioms {name}_eval\n'
s+=f'def fixed : List Link := {lit(legacy)}\n'
s+='''theorem legacy_eval : legacyLinks = fixed := by
  unfold legacyLinks
  rw [sponge_eval,private_eval,append_eval]
  rfl
#print axioms legacy_eval
end PV_B3P_LegacyValues133
'''
p=D/'PV_B3P_LegacyValues133.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
