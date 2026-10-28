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
retained=[(k,p+48 if p>=864 else p,c+48 if c>=864 else c) for k,p,c in legacy if not k]
forestpath=[]
for l in range(24):
 a=912+l//4*16+1+4*(l%4)
 b=(4+l if l<=20 else 33+l)
 prev=3 if l==0 else (4+l-1 if l-1<=20 else 33+l-1)
 forestpath += [(True,prev*16+11,a),(True,a+1,b*16+12),(True,a+1,b*16)]
forest=retained+forestpath
s='''import PV_B3P_LegacyValues133
namespace PV_B3P_ForestValues133
open PV_B3P_Schedule133 PV_B3P_LegacyValues133
set_option autoImplicit false
'''
s+=f'def retained : List Link := {lit(retained)}\n'
chunks=[legacy[i:i+8] for i in range(0,len(legacy),8)]
for i,chunk in enumerate(chunks):
 rc=[(k,p+48 if p>=864 else p,c+48 if c>=864 else c) for k,p,c in chunk if not k]
 s+=f'def chunk{i} : List Link := {lit(chunk)}\ntheorem chunk{i}_eval : (chunk{i}.filter (fun x => !x.path)).map translate = {lit(rc)} := rfl\n#print axioms chunk{i}_eval\n'
s+='theorem retained_eval : (PV_B3P_LegacyValues133.fixed.filter (fun x => !x.path)).map translate = retained := by\n'
s+='  have split : PV_B3P_LegacyValues133.fixed = '+ ' ++ '.join(f'chunk{i}' for i in range(len(chunks)))+' := rfl\n'
s+='  rw [split]\n  simp only [List.filter_append,List.map_append,'+','.join(f'chunk{i}_eval' for i in range(len(chunks)))+']\n  rfl\n#print axioms retained_eval\n'
s+=f'def pathFixed : List Link := {lit(forestpath)}\n'
s+='''theorem paths_eval : (List.range 24).flatMap (fun level =>
    let previous := if level == 0 then 3 else forestBlock (level-1)
    [path (previous*16+11) (forestAux level),
     path (forestAux level+1) (forestBlock level*16+12),
     path (forestAux level+1) (forestBlock level*16)]) = pathFixed := rfl
#print axioms paths_eval
'''
s+=f'def fixed : List Link := {lit(forest)}\n'
s+='''theorem forest_eval : forestLinks legacyLinks = fixed := by
  rw [PV_B3P_LegacyValues133.legacy_eval]
  unfold forestLinks
  rw [retained_eval,paths_eval]
  rfl
#print axioms forest_eval
end PV_B3P_ForestValues133
'''
p=D/'PV_B3P_ForestValues133.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
# A block proves at most four check iterations; prior counts are explicit data.
# No monolithic reduction of the entire recurrence is generated.
for name,xs,imp in [('Legacy',legacy,'Legacy'),('Forest',forest,'Forest')]:
 ns=f'PV_B3P_{name}Capacity133';v=f'PV_B3P_{name}Values133'
 s=f'import {v}\nnamespace {ns}\nopen PV_B3P_Schedule133\nset_option autoImplicit false\n'
 count=0
 for start in range(0,len(xs),4):
  end=min(start+4,len(xs));chunk=xs[start:end];ps=[p for _,p,_ in xs[:start]][::-1];cs=[c for _,_,c in xs[:start]][::-1]
  np=[p for _,p,_ in xs[:end]][::-1];nc=[c for _,_,c in xs[:end]][::-1]
  s+=f'theorem step{count} (tail : List Link) :\n    checkEndpoints ({lit(chunk)} ++ tail) {ps} {cs} =\n    checkEndpoints tail {np} {nc} := by rfl\n#print axioms step{count}\n'
  count+=1
 s+=f'theorem success : checkEndpoints {v}.fixed [] [] = .ok () := by\n  calc\n'
 for i,start in enumerate(range(0,len(xs),4)):
  end=min(start+4,len(xs));np=[p for _,p,_ in xs[:end]][::-1];nc=[c for _,_,c in xs[:end]][::-1]
  if i==0:s+=f'    checkEndpoints {v}.fixed [] [] = checkEndpoints {lit(xs[end:])} {np} {nc} := step{i} _\n'
  else:s+=f'    _ = checkEndpoints {lit(xs[end:])} {np} {nc} := step{i} _\n'
 s+='    _ = .ok () := rfl\n#print axioms success\nend '+ns+'\n'
 p=D/f'{ns}.lean'
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
# Endpoint flat-map is certified eight links at a time before sorting.
ns='PV_B3P_Sorted133'
s='''import PV_B3P_ForestValues133
namespace PV_B3P_Sorted133
open PV_B3P_Schedule133
set_option autoImplicit false

def endpoints (links : List Link) : List Nat := links.flatMap (fun x => [x.producer,x.consumer])
'''
chunks=[forest[i:i+8] for i in range(0,len(forest),8)]
for i,chunk in enumerate(chunks):
 eps=[v for _,p,c in chunk for v in [p,c]]
 s+=f'def chunk{i} : List Link := {lit(chunk)}\ntheorem chunk{i}_eval : endpoints chunk{i} = {eps} := rfl\n#print axioms chunk{i}_eval\n'
eps=[v for _,p,c in forest for v in [p,c]];expected=sorted(set(eps));assert len(expected)==214
def rightappend(parts):
 return parts[0] if len(parts)==1 else parts[0]+' ++ ('+rightappend(parts[1:])+')'
s+='def input : List Nat := '+rightappend([str(eps[i:i+16]) for i in range(0,len(eps),16)])+'\n'
s+='def expected : List Nat := '+ rightappend([str(expected[i:i+16]) for i in range(0,len(expected),16)])+'\n'
s+='theorem endpoints_eval : endpoints PV_B3P_ForestValues133.fixed = input := by\n'
s+='  have split : PV_B3P_ForestValues133.fixed = '+' ++ '.join(f'chunk{i}' for i in range(len(chunks)))+' := rfl\n'
s+='  rw [split]\n  simp only [endpoints,List.flatMap_append]\n  change '+ ' ++ '.join(f'endpoints chunk{i}' for i in range(len(chunks)))+' = input\n'
s+='  rw ['+','.join(f'chunk{i}_eval' for i in range(len(chunks)))+']\n  simp only [List.append_assoc]\n  rfl\n'
s+='''end PV_B3P_Sorted133
'''
p=D/f'{ns}.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
