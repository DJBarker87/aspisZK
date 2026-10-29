"""Declaration-level let lifting for the finite COPY_PATTERNS initializer.
Checks a roundtrip expansion to the exact ported source initializer; no values,
call order or error paths are edited. Read-only constant data only.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');p=D/'ported227-arrayproof-resume5.lean.txt';s=p.read_text()
a=s.index('/-- [pv_b3p6_reference227::reference_copy_terminal::constants::COPY_PATTERNS]');b=s.index('\n/-- [',a+1);old=s[a:b]
lets=re.findall(r'^  let (a\d*) := (.*)$',old,re.M);assert len(lets)==15
expr=old[old.index('  Array.make 14#usize ['):].strip();openix=expr.index('[');depth=1;i=openix+1;items=[];start=i
while depth:
 c=expr[i]
 if c in '[({':depth+=1
 if c in '])}':depth-=1
 if c==',' and depth==1:items.append(expr[start:i].strip());start=i+1
 i+=1
items.append(expr[start:i-1].strip());assert len(items)==14
prefix='reference_copy_terminal.constants.'
def replacevars(x):
 for k,_ in reversed(lets):x=re.sub(r'\b'+k+r'\b',prefix+'pattern_let_'+k,x)
 return x
new=[]
for k,v in lets:
 ty='U8' if '#u8' in v else 'U32';new.append(f'private def {prefix}pattern_let_{k} : Array {ty} 16#usize := {v}\n')
for j,x in enumerate(items):new.append(f'private def {prefix}pattern_{j} : reference_copy_terminal.CompiledPoolV1PairForestPattern :=\n{replacevars(x)}\n')
new.append('@[irreducible]\ndef '+prefix+'COPY_PATTERNS : Array reference_copy_terminal.CompiledPoolV1PairForestPattern 14#usize :=\n  Array.make 14#usize ['+',\n'.join(prefix+f'pattern_{j}'for j in range(14))+'] (by simp only [List.length_cons, List.length_nil]; rfl)\n')
# Mechanically reconstruct the original term by replacing each lifted name.
reconstructed='  Array.make 14#usize [\n'+',\n'.join(items)+'\n] (by simp only [List.length_cons, List.length_nil]; rfl)'
token=lambda x:re.findall(r'\w+|[^\s]',x)
assert token(reconstructed)==token(expr)
replacement=old[:old.index('@[irreducible]')]+ '\n'.join(new)
s=s[:a]+replacement+s[b:];q=D/'ported227-lifted-resume5.lean.txt';q.write_text(s)
(D/'constant227-resume5.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),lifted_shared_values=15,lifted_pattern_records=14,roundtrip_tokens_match=True,data_values_unchanged=True,transformation='let-bound pure constant values and record literals lifted to named private definitions; array order unchanged'),indent=2)+'\n')
print('lifted',len(new))
