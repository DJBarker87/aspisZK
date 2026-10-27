"""Generate small symbolic first-bind certificates, never evaluate a whole run.
The candidate list is a syntactic preflight, not execution-reachability credit.
"""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2]
p=R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'
s=(p/'ProverRwFullFuns.lean').read_text()
s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
ms=list(re.finditer(r'^def\s+([^\s{(:]+)',s,re.M))
d={m[1]:s[m.end():ms[i+1].start() if i+1<len(ms) else len(s)] for i,m in enumerate(ms)}
# Strip intervening attributes/comments: only parse the header before :=.
alias={m[1]:int(m[2]) for m in re.finditer(r'^abbrev (\S+) .*:= @ExternalFuns.op(\d+) ',(p/'ProverRwFullExternalFuns.lean').read_text(),re.M)}
pat=re.compile(r'(?<![\w.])(?:'+'|'.join(re.escape(n) for n in sorted(d,key=len,reverse=True))+r')(?![\w.])')
g={n:set(pat.findall(b)) for n,b in d.items()}
seen=set();todo=['RealR1_client.prove_for_proof_accounts']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(g[n]-seen)
rows=[]
for n in sorted(seen,key=lambda n:(n!='prover.retry_attempt',n)):
 b=d[n]
 if ':= do\n' not in b:continue
 header,body=b.split(':= do\n',1)
 m=re.match(r'  if (.*?)\n  then\n',body,re.S)
 if not m:continue
 expr=m[1]
 rest=body[m.end():]
 cut=rest.find('\n  else\n')
 if cut<0:continue
 yes=rest[:cut]
 no=rest[cut+len('\n  else\n'):]
 no=re.split(r'\npartial_fixpoint|\n@\[',no)[0].strip('\n')
 # Header binders, balanced; terminate at the return-type colon.
 pos=0;names=[];binders=[];valid=True
 while True:
  while pos<len(header) and header[pos].isspace():pos+=1
  if pos>=len(header) or header[pos]==':':break
  if header[pos] not in '({[':valid=False;break
  start=pos;stack=[]
  while pos<len(header):
   c=header[pos]
   if c in '({[':stack.append(c)
   elif c in ')}]':
    stack.pop()
    if not stack:pos+=1;break
   pos+=1
  binder=header[start:pos];ns=binder[1:-1].split(':',1)[0].split()
  if any(not re.fullmatch(r'\w+',v) for v in ns):valid=False;break
  names+=ns;binders.append(binder)
 if not valid:continue
 ix=len(rows)
 if ix>=13:break
 module=f'PV_RE_Guard{ix:03}'
 resultType=header[pos+1:].strip()
 args=' '.join('('+v+' := '+v+')' for v in names)
 binderText=' '.join(binders)
 text=f'''import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.{module}
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def onTrue {binderText} : {resultType} := do
{yes}

def onFalse {binderText} : {resultType} := do
{no}

/-- Exact first guard of `{n}`.
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {' '.join(binders)} :
  {n} {args} =
    (if {expr} then onTrue {args} else onFalse {args}) := by
  rw [{n}]
  rfl

#print axioms onTrue
#print axioms onFalse
#print axioms first
end R1Z.{module}
'''
 path=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(module+'.lean')
 if "--check" in sys.argv:
  assert path.read_text()==text,path
 else:path.write_text(text)
 rows.append(dict(module='R1Z/'+module,function=n,first_guard=expr,sha256=hashlib.sha256(text.encode()).hexdigest(),claim='symbolic exact first bind only; fixture entry unresolved'))
manifest=R/'evidence/pv-reach-20261027/guard-manifest.json'
if '--check' in sys.argv:assert json.loads(manifest.read_text())==rows
else:manifest.write_text(json.dumps(rows,indent=2)+'\n')
print('Candidate guard modules:',len(rows))
