"""Check the actual source shapes consumed by the concrete new loop laws.
This associates SOURCE with the handwritten loop model; compiler preservation
remains V370 at D381/D386. No machine-code equality is asserted.
"""
from pathlib import Path
import re,hashlib,json,sys
D=Path('evidence/pv-b3p6-20261028');P=Path('tools/pv-b3p6-20261028/v244');O=D/'resume9'
token=lambda s:re.findall(r'\w+|[^\s]',re.sub(r'//[^\n]*|/\*[\s\S]*?\*/','',s))
def body(s,name):
 a=s.index('fn '+name+'(');bs=s.index('{',a);depth=1;i=bs+1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
source=(P/'host_terminal.rs').read_text();owned=(P/'reference_terminal.rs').read_text()
assert (Path('crates/aspis-r1-cost-probe/src/host_terminal.rs').read_bytes()==(P/'host_terminal.rs').read_bytes())
rows=[]
for name,initial,index,bound,statement,sequence,proof in [
 ('equality_value','let mut product = equality_factor(left[0], right[0]);',1,'index < left.len()','product = product.mul(equality_factor(left[index], right[index]));',list(range(1,10)),'PV_B3P_Binding9227.equality_body_binding'),
 ('reconstruct_10','let mut acc = view[9];',9,'index > 0','acc = acc.add(acc).add(view[index]);',list(reversed(range(9))),'PV_B3P_Binding9227.reconstruct_body_binding')]:
 src=body(source,name);ref=body(owned,name)
 stem='product'if name=='equality_value'else'acc'
 loop=(f'while {bound} {{ {statement} index += 1; }}'if name=='equality_value'else f'while {bound} {{ index -= 1; {statement} }}')
 assert token(loop)==token(src[src.index('while '):src.rindex('}')].rsplit(stem,1)[0].strip()),name
 expanded='\n'.join(re.sub(r'\bindex\b',str(i)+'usize',statement)for i in sequence)
 model=src[:src.index('while ')]+expanded+'\n    '+stem+'\n}'
 # Equality's dedicated rewrite removes the dead index binding. Reconstruct retains it.
 if name=='equality_value':model=model.replace('let mut index = 1usize;','')
 # Literal 0/1 in the owned equality expansion have inferred usize, so canonicalize suffixes.
 canonical=lambda t:[re.sub(r'^(\d+)usize$',r'\1',x)for x in token(t)]
 assert canonical(model)==canonical(ref),name
 rows.append(dict(body=name,source_line=source[:source.index('fn '+name+'(')].count('\n')+1,source_sha256=hashlib.sha256(src.encode()).hexdigest(),owned_sha256=hashlib.sha256(ref.encode()).hexdigest(),statement=statement,iteration_indices=sequence,theorem=proof,match='exact token equality after only the named fixed-loop expansion and dead index removal',preserves=['initial read/factor','counter guard and bounds','operand evaluation order','all calls and constants','every Result tag'],array_extent=10 if name=='equality_value' else 16,loop_model='usize_body with stop10'if name=='equality_value'else'reverse_body with decrement before reads'))
record=dict(semantic_use='reclassification within existing Charon/Aeneas tool trust',classification='structural; chained field arithmetic',rows=rows,source_to_machine='V370 / pending owner D381,D386 retained; machine-code correspondence not required under own-1',deployed_features='native227-composition-features.json',deployed_source_freeze='native227-composition-source-freeze.json',native_differential='reused64/36 observations; finite validation only; no new native run')
p=O/'concrete-source-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(source_bindings=len(rows),whole_row_closed=False)))
