"""Bounded source-input certificates with opaque named tails (not whole-suffix reduction)."""
from pathlib import Path
import re,json,sys
P=Path(__file__).resolve().parent;R=P.parents[1];old=R/'evidence/joint-fixture11-20261026/JFm_UNCHECKED'
s=(old/'JFm_Q25Source.lean.txt').read_text().replace('JFm_Q25','JFu_Q25').replace('import JFu_Q25Hashes','import JFu_Q25Aggregate\nimport JFu_Q25Reads')
base=s[:s.index('def rest00')]
files={R/'lean/JFu_Q25InputBase.lean':base+'end Input\nend AspisR1.JFu_Q25Source\n'}
start='set_option autoImplicit false\nnamespace AspisR1.JFu_Q25Source\nopen Aeneas Aeneas.Std Result\nopen AspisR1PublicPreparation\nopen AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge\nnamespace Input\n'
end='end Input\nend AspisR1.JFu_Q25Source\n'
row=json.loads((R/'evidence/joint-fixture11-20261026/JFm_WINDOWS.json').read_text())[25]
segs=[row['before']+[0,185]+row['frame'][:5]]+[row['frame'][5+j:5+j+32] for j in range(0,3712,32)]
suffixes=[f'suffix{i:03}' for i in range(len(segs))]
rest='import JFu_Q25InputBase\n'+start
for i in reversed(range(len(segs))):
 rest+=f'def suffix{i:03} : List Nat := n{i:02}'+(f' ++ suffix{i+1:03}' if i+1<len(segs) else '')+'\n'
attrs='attribute [local irreducible] '+' '.join(suffixes)+'\n'
rest+=attrs
positions=[]
for b in range(59):
 offset=64*b;j=0
 while offset>=len(segs[j]):offset-=len(segs[j]);j+=1
 positions.append((j,offset))
 rest+=f'def rest{b:02} : List Nat := '+(f'(n{j:02}.drop {offset})' if offset else f'n{j:02}')+f' ++ suffix{j+1:03}\n'
rest+='theorem numeric_eq : numeric=rest00 := by\n  simp only [numeric,rest00,List.append_assoc,'+','.join(suffixes[1:])+']\n#print axioms numeric_eq\n'
files[R/'lean/JFu_Q25InputRest.lean']=rest+end
steps={}
for b in range(58):
 j,offset=positions[b];todo=64;terms=[]
 while todo>0:
  terms.append(f'(n{j:02}.drop {offset})' if offset else f'n{j:02}')
  todo-=len(segs[j])-offset;j+=1;offset=0
 drop=len(segs[j-1])+todo
 left=' ++ '.join(terms);right=f'JFu_Q25Absorb.B{b:02}.input ++ (n{j-1:02}.drop {drop})'
 # Only the one/two intermediate suffix definitions are expanded; the common tail is opaque.
 first,_=positions[b]
 unfold=','.join(f'suffix{k:03}' for k in range(first+1,j))
 steps[b]=f'''theorem step{b:02} : rest{b:02}=JFu_Q25Absorb.B{b:02}.input ++ rest{b+1:02} := by
  have cell : {left}={right} := by rfl
  simpa only [rest{b:02},rest{b+1:02},{unfold},List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix{j:03}) cell
#print axioms step{b:02}
'''
groups=[(0,1)]+[(b,min(b+8,58)) for b in range(1,58,8)]
for a,b in groups:
 files[R/f'lean/JFu_Q25InputSteps{a:02}.lean']='import JFu_Q25InputRest\n'+start+attrs+''.join(steps[i] for i in range(a,b))+end
final=''.join(f'import JFu_Q25InputSteps{a:02}\n' for a,b in groups)+start+attrs
final+='theorem last : rest58=JFu_Q25Absorb.tail := by\n  simp only [rest58,suffix116,n115,n116]\n  rfl\n#print axioms last\n'
regroup=s[s.index('theorem regroup'):s.index('theorem native')].replace('  change rest00=','  rw [numeric_eq]\n  change rest00=')
final+=regroup+s[s.index('theorem native'):s.index('theorem absorbInput')]
final+='end AspisR1.JFu_Q25Source\n'
files[R/'lean/JFu_Q25Input.lean']=final
pos=s.index('theorem absorbInput')
files[R/'lean/JFu_Q25Source.lean']='import JFu_Q25Input\n'+start.replace('namespace Input\n','')+s[pos:]
for f,t in files.items():
 if '--check' in sys.argv:assert f.read_text()==t,f
 else:f.write_text(t)
print('source preflight',len(files),'files; max8 local regroup cells/module; named opaque common suffix')
