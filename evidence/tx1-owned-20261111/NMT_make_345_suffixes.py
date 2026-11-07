from pathlib import Path
import re,textwrap,json
E=Path(__file__).resolve().parent
src=(E/'NMT_stage1_owned.Funs.lean').read_text()
start=src.index('  := do\n',src.index('def r1_pool_adapter.owned.stage1_owned ('))+len('  := do\n')
src=src[start:];src=src[:src.index('\n  else\n    let b1 ←')]
# Use the first literal branch; Route10 proves both admitted branches identical.
lines=src.splitlines();cont=[]
for match in re.finditer(r'core\.ops\.control_flow\.ControlFlow\.Continue\s+(\w+)\s*=>\n',src):
 a=src[:match.start()].count('\n');b=src[:match.end()].count('\n')
 pat=a
 while not lines[pat].lstrip().startswith('|'):pat-=1
 indent=len(lines[pat])-len(lines[pat].lstrip())
 end=b
 while end<len(lines):
  l=lines[end]
  if l.strip() and len(l)-len(l.lstrip())<=indent:break
  end+=1
 body=textwrap.dedent('\n'.join(lines[b:end]));cont.append((match[1],body))
assert [v for v,b in cont]==['_','_','_','_','val','_','val1','val2','_','val3','val4','val5','val6'],[v for v,b in cont]
frames='''import NMT_345CheckpointData
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
structure PublicData (W : Type) extends CheckpointData W where
 publicData : Slice U8
structure Decoded (W : Type) extends PublicData W where
 statement : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
structure Candidate (W : Type) extends Decoded W where
 candidate : Array U8 688#usize
structure ProofData (W : Type) extends Candidate W where
 proofData : Slice U8
structure Bounds (W : Type) extends ProofData W where
 proofStart : Usize
 proofEnd : Usize
structure Returned (W : Type) extends Bounds W where
 checkpoint : alloc.vec.Vec U8
end NMT_345
'''
(E/'NMT_345Frames.lean').write_text(frames)
base={'program_id':'parent.program','accounts':'parent.accounts','data':'parent.data',
 'proof_account':'parent.proofAccount','public_account':'parent.publicAccount','checkpoint_account':'parent.checkpointAccount'}
phases=['Selected']*4+['CheckpointData']*2+['PublicData','Decoded','Decoded','Candidate','ProofData','Bounds','Returned']
for i,((v,body),phase) in enumerate(zip(cont,phases)):
 mapping=dict(base)
 for limit,name,field in [(4,'val','checkpointData'),(6,'val1','publicData'),(7,'val2','statement'),(9,'val3','candidate'),(10,'val4','proofData'),(11,'val5','proofEnd'),(11,'proof_start','proofStart'),(12,'val6','checkpoint')]:
  if i>=limit:mapping[name]='parent.'+field
 for n in range(17):mapping['NMT_call_'+str(n)]='c.c'+str(n)
 body=re.sub(r'(?<![.\w])('+ '|'.join(sorted(mapping,key=len,reverse=True))+r')\b',lambda m:mapping[m[1]],body)
 mod=f'NMT_345Raw_{i:02}'
 text='''import NMT_345Frames
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
'''+f'''/-- Verbatim E003 continuation at emitted Try occurrence {i}; only local
captures are projected from the single complete parent state. -/
def raw{i:02} {{W : Type}} (c : Calls) (parent : {phase} W) : Result Ret := do
'''+textwrap.indent(body,' ')+'\nend NMT_345\n'
 (E/(mod+'.lean')).write_text(text)
body=textwrap.dedent(src[src.index('      let r ←'):])
for name,target in sorted(base.items(),key=lambda x:-len(x[0])):
 body=re.sub(r'(?<![.\w])'+name+r'\b',target,body)
for n in reversed(range(17)):body=re.sub(r'\bNMT_call_'+str(n)+r'\b',f'c.c{n}',body)
(E/'NMT_345RawSelected.lean').write_text('''import NMT_345Frames
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
def rawSelected {W : Type} (c : Calls) (parent : Selected W) : Result Ret := do
'''+textwrap.indent(body,' ')+'\nend NMT_345\n')
(E/'NMT_345_SUFFIXES.json').write_text(json.dumps([dict(module=f'NMT_345Raw_{i:02}',phase=p,returned=v,lines=len(b.splitlines()))for i,((v,b),p)in enumerate(zip(cont,phases))],indent=1)+'\n')
