"""Name exact post-bind computations; do not turn them into reachability claims."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2]
s=(R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean').read_text()
s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
ms=list(re.finditer(r'^def\s+([^\s{(:]+)',s,re.M));d={m[1]:s[m.end():ms[i+1].start() if i+1<len(ms) else len(s)] for i,m in enumerate(ms)}
old=[]
for file in ['prefix-manifest.json','callee-manifest.json']:
 old+=json.loads((R/'evidence/pv-reach-20261027'/file).read_text())
rows=[]
for ix,row in enumerate(old):
 n=row['function'];header,body=d[n].split(':= do\n',1)
 m=re.match(r'  let (\([^\n]+\)|\w+) ←\s*\n?\s*(\S+)',body);assert m,n
 end=re.search(r'\n  (?:let |if |match |ok |[A-Za-z_])',body[m.end():]);stop=m.end()+end.start() if end else len(body)
 expr=body[body.index('←')+1:stop].strip();rest=body[stop:];rest=re.split(r'\npartial_fixpoint|\n@\[',rest)[0].strip('\n');rest=re.sub(r'\nend ProverRwFull\s*$','',rest)
 pos=0;names=[];binders=[]
 while True:
  while pos<len(header) and header[pos].isspace():pos+=1
  if header[pos]==':':break
  start=pos;stack=[]
  while pos<len(header):
   c=header[pos]
   if c in '({[':stack.append(c)
   elif c in ')}]':
    stack.pop()
    if not stack:pos+=1;break
   pos+=1
  binder=header[start:pos];names+=binder[1:-1].split(':',1)[0].split();binders.append(binder)
 args=' '.join('('+v+' := '+v+')' for v in names)
 errName='pvFailure' if 'e' in names else 'e'
 mod=f'PV_RE_Continue{ix:03}';rtype=header[pos+1:].strip();bs=' '.join(binders)
 text=f'''import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.{mod}
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {{α : Type}} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `{n}`.
Recursive calls remain the original extracted calls. -/
def continueAfter {bs} (out : Payload ({expr})) : {rtype} := do
  let {m[1]} := out
{rest}

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation {bs} :
    {n} {args} =
      ({expr} >>= fun out => continueAfter {args} out) := by
  rw [{n}]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success {bs} (out : Payload ({expr}))
    (h : ({expr}) = .ok out) :
    {n} {args} = continueAfter {args} out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure {bs} ({errName} : Error)
    (h : ({expr}) = .fail {errName}) :
    {n} {args} = .fail {errName} := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges {bs}
    (h : ({expr}) = .div) :
    {n} {args} = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.{mod}
'''
 path=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(mod+'.lean')
 if '--check' in sys.argv:assert path.read_text()==text,path
 else:path.write_text(text)
 rows.append(dict(module='R1Z/'+mod,function=n,first_expression=expr,sha256=hashlib.sha256(text.encode()).hexdigest(),native_guard_instantiated=False,claim='exact named continuation and Result transitions, not whole-run callback membership'))
p=R/'evidence/pv-reach-20261027/resume/continuation-manifest.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==rows
else:p.write_text(json.dumps(rows,indent=2)+'\n')
print('exact continuation modules',len(rows))
