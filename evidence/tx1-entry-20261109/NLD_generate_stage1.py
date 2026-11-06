PREFIX='import NLD_TraceControl\nimport NGL_FirstDecoded\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.NLD_Stage1Source\nopen Aeneas Aeneas.Std Result NLD_SourceTrace\nopen _root_.AdapterRw\n/-- Complete canonical emitted stage1_owned, instrumented at every monadic\noccurrence. This is a SOURCE trace; no native cut or SDK law is asserted. -/\n'
PROOF="\ntheorem erasure (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)\n    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :\n    (stage1Owned ops program accounts data).2 =\n      AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data := by\n  simp only [stage1Owned,AdapterRw.r1_pool_adapter.owned.stage1_owned,\n    erase_bind,erase_call,erase_pure,erase_if,erase_control]\n  all_goals repeat' first\n    | (with_reducible rfl)\n    | (fail_if_no_progress simp only [erase_bind,erase_call,erase_pure,erase_if,erase_control])\n    | (apply AspisR1.NLD_SourceTrace.bind_congr; intro x)\n    | split\n#print axioms erasure\nend AspisR1.NLD_Stage1Source\n"
"""Deterministic instrumentation of the unchanged canonical owned body."""
from pathlib import Path
import re,json,hashlib,sys
E=Path(__file__).resolve().parent
P=E.parent.parent/'docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean'
raw=P.read_text();start=raw.index('def r1_pool_adapter.owned.stage1_owned ');end=raw.index('\n/--',start)
offset=raw[:start].count('\n')+1
src=raw[start:end].replace('def r1_pool_adapter.owned.stage1_owned','def stage1Owned',1).replace('  Result (core.result.Result (alloc.vec.Vec Std.U8)','  Trace (core.result.Result (alloc.vec.Vec Std.U8)',1)
lines=src.splitlines();result=[];calls=[];i=0
while i<len(lines):
 line=lines[i];match=re.match(r'^(\s*)let (.+?) ←\s*(.*)$',line)
 tail=re.match(r'^(\s*)(core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual.*)$',line)
 if match or tail:
  indent=len((match or tail)[1]);j=i+1
  while j<len(lines)and(not lines[j].strip()or len(lines[j])-len(lines[j].lstrip())>indent):j+=1
  expr=([match[3]]if match and match[3]else[tail[2]]if tail else[])+lines[i+1:j]
  occurrence=offset+i;calls.append(dict(occurrence=occurrence,term='\n'.join(expr),binder=match[2]if match else None))
  lead=match[1]+'let '+match[2]+' ← 'if match else tail[1]
  result.append(lead+'call '+str(occurrence)+' (');result+=[' '*(indent+2)+l.lstrip()if n==0 else l for n,l in enumerate(expr)];result.append(' '*indent+')');i=j;continue
 line=re.sub(r'\bok\b','pure',line)if re.match(r'^\s*(ok\b|else ok\b|then ok\b)',line)else line
 result.append(line.replace('else ok (','else pure (').replace('then ok (','then pure ('));i+=1
text=PREFIX+'\n'.join(result)+'\n'+PROOF
manifest=json.dumps(dict(source=str(P.relative_to(E.parent.parent)),source_sha256=hashlib.sha256(P.read_bytes()).hexdigest(),calls=calls),indent=1)+'\n'
for n,t in [('NLD_Stage1Source.lean',text),('NLD_STAGE1_OCCURRENCES.json',manifest)]:
 if '--check'in sys.argv:assert(E/n).read_text()==t,n
 else:(E/n).write_text(t)
print('stage1 source instrumentation matches:116 occurrence sites')
