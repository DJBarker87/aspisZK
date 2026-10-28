"""Generate one combined axiom audit and one separate focused closure replay."""
from pathlib import Path
import re,json,hashlib,sys
D=Path(__file__).resolve().parent;L=D/'lean'
roots=['PV_B3_TypeFrame134','PV_B3_Close134','PV_B3_Install222','PV_B3_Structural222','PV_B3_StructuralArithmetic','PV_B3_ReverseRangeD336','PV_B3_Install117','PV_B3_Install121']
seen=set();order=[]
def visit(m):
 assert not m.startswith('XR'),m
 if m in seen or not m.startswith('PV_B3_'):return
 seen.add(m);p=L/(m+'.lean');assert p.is_file(),m
 for imp in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(imp)
 order.append(m)
for m in roots:visit(m)
names=[]
for m in order:
 stack=[]
 for line in (L/(m+'.lean')).read_text().splitlines():
  n=re.match(r'^namespace\s+(\S+)',line)
  if n:stack.append(n[1]);continue
  if re.match(r'^(?:noncomputable\s+)?section(?:\s|$)',line):stack.append(None);continue
  if re.match(r'^end(?:\s|$)',line):
   if stack:stack.pop()
   continue
  n=re.match(r'^\s*(?:noncomputable\s+)?theorem\s+([\w.]+)',line)
  if n:names.append('.'.join([x for x in stack if x]+[n[1]]))
head=''.join('import '+m+'\n'for m in roots)
audit=head+'\n-- Every theorem in the private closing cone, including preservation fields.\n'+''.join('#print axioms '+n+'\n'for n in dict.fromkeys(names))
# The final replay composes all four replacements on one original carrier.
body='''
namespace PV_B3_ClosureD336
open Aeneas Aeneas.Std Result ProverRwFull PV_B3_ArrayCarrier
set_option autoImplicit false
noncomputable section
abbrev Types := PV_B3_Close134.Types
abbrev Q := ProverRwFull.aspis_core.field.QM31

def installed (base : ExternalTypes) (ops : @ExternalFuns (Types base)) : @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  PV_B3_Install121.selected (PV_B3_Install117.selected
    (PV_B3_Install222.selected (PV_B3_Close134.install base ops)))

theorem op134 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op134 (Types base) (installed base ops) = ok (.Ok R1Z.PV_Op134_Masks.masks) :=
  PV_B3_Close134.source base ops

theorem op222 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (column : Slice Q) (point : Array Q 10#usize) :
    @ExternalFuns.op222 (Types base) (installed base ops) column point =
      resultMap (Option.map PV_B3_Install222.fromCopy)
        (PV_B3_MultilinearFinite222.evaluate (PV_B3_Install222.sliceMap PV_B3_Install222.intoCopy column)
          (arrayMap PV_B3_Install222.intoCopy point)) := by
  letI : ExternalTypes := Types base
  exact PV_B3_Install222.source (PV_B3_Close134.install base ops) column point

theorem op117 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (c : Array Q 16#usize) (m : Array Q 10#usize) (g : Q) (p : Array Q 10#usize) :
    @ExternalFuns.op117 (Types base) (installed base ops) c m g p =
      PV_B3_Carrier117.map PV_B3_Carrier117.toQ
        (PV_B3_AuditSourceD324.Mask117.reference (PV_B3_Carrier117.fromArray c)
          (PV_B3_Carrier117.fromArray m) (PV_B3_Carrier117.fromQ g) (PV_B3_Carrier117.fromArray p)) := by
  letI : ExternalTypes := Types base
  exact PV_B3_Install117.source (PV_B3_Install222.selected (PV_B3_Close134.install base ops)) c m g p

theorem op121 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (poly : Array Q 28#usize) (x : Q) :
    @ExternalFuns.op121 (Types base) (installed base ops) poly x =
      PV_B3_Carrier117.map PV_B3_Carrier117.toQ
        (PV_B3_AuditSourceD324.Poly121.reference (PV_B3_Carrier117.fromArray poly) (PV_B3_Carrier117.fromQ x)) := by
  letI : ExternalTypes := Types base
  exact PV_B3_Install121.source (PV_B3_Install117.selected
    (PV_B3_Install222.selected (PV_B3_Close134.install base ops))) poly x

#print op134
#print op222
#print op117
#print op121
#print axioms op134
#print axioms op222
#print axioms op117
#print axioms op121
'''
fields=re.findall(r'^  (op\d+)(?:\s|\{|\()',Path('docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean').read_text(),re.M)
for f in fields:
 if f in ['op134','op222','op117','op121']:continue
 body+=f'theorem preserved_{f} (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :\n    @ExternalFuns.{f} (Types base) (installed base ops) = @ExternalFuns.{f} (Types base) ops := rfl\n#print axioms preserved_{f}\n'
body+='end\nend PV_B3_ClosureD336\n'
outputs={L/'PV_B3_AuditD336.lean':audit,L/'PV_B3_ClosureD336.lean':head+body}
for p,s in outputs.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
meta=dict(roots=roots,private_cone=order,audit_declarations=list(dict.fromkeys(names)),preserved_combined_fields=len(fields)-4,XR_imports=False,targets={p.name:hashlib.sha256(s.encode()).hexdigest()for p,s in outputs.items()})
if '--check' not in sys.argv:(D/'d336-closure-manifest.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(modules=len(order),axiom_queries=len(set(names)),preserved_fields=len(fields)-4)))
