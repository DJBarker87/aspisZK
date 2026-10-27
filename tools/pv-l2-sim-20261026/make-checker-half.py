"""Fission the extracted half check at named arithmetic boundaries."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
S=(B/'CertCheckExtracted.lean').read_text();CHECK='--check' in sys.argv
half=S.split('def half_ok ',1)[1].split(' := do\n',1)[1].split('\n/--',1)[0]
def part(start,end):return half[half.index('  let '+start):half.index('  let '+end)]
rows=[
 ('MM','(x y : U32)','U64',S.split('def mm ',1)[1].split(' := do\n',1)[1].split('\n/--',1)[0].replace('  i2 % P','  let out ← i2 % P\n  ok out'),{}),
 ('HalfShift','(a : Slice U32)','U32',part('i ←','x1 ←')+'  ok x01\n',{}),
 ('HalfInputs','(a h : Slice U32)','(U32 × U32 × U32 × U32) × (U32 × U32 × U32 × U32)',
  '  let x01 ← half_shift a\n'+part('x1 ←','i5 ←')+'  ok ((x01,x1,x2,x3),(y0,y1,y2,y3))\n',{'half_shift':('HalfShift','recorded','source','erases')}),
 ('HalfPQ','(x2 x3 y2 y3 : U32)','U64 × U64',part('i5 ←','i12 ←')+'  ok (p,q)\n',{'mm':('MM','recorded','mm','erases')}),
 ('HalfR0','(x01 x1 y0 y1 : U32) (p q : U64)','U64',part('i12 ←','i20 ←')+'  ok r0\n',{'mm':('MM','recorded','mm','erases')}),
 ('HalfR1','(x01 x1 y0 y1 : U32) (p q : U64)','U64',part('i20 ←','i26 ←')+'  ok r1\n',{'mm':('MM','recorded','mm','erases')}),
 ('HalfR2','(x01 x1 x2 x3 y0 y1 y2 y3 : U32)','U64',part('i26 ←','i35 ←')+'  ok r2\n',{'mm':('MM','recorded','mm','erases')}),
 ('HalfR3','(x01 x1 x2 x3 y0 y1 y2 y3 : U32)','U64',half[half.index('  let i35 ←'):half.index('  ok (((')]+'  ok r3\n',{'mm':('MM','recorded','mm','erases')}),
]
def emit(p,s):
 if CHECK:
  if not p.exists() or p.read_text()!=s:raise SystemExit('stale '+str(p))
 else:p.write_text(s)
for num,(mod,params,result,source,callees) in enumerate(rows,30):
 rec=[];sourceLines=[]
 for line in source.splitlines():
  if line.startswith('  ok '):
   rec.append('  PV_L2_Record.pure '+line[5:]);sourceLines.append(line);continue
  match=re.fullmatch(r'  let (\w+) ← (.*)',line)
  if not match:raise ValueError(line)
  var,expr=match.groups();op=expr.split()[0]
  if op in callees:
   module,record,original,_=callees[op];args=expr.split(' ',1)[1]
   rec.append(f'  let {var} ← PV_L2_F6{module}.{record} {args}')
   sourceLines.append(f'  let {var} ← '+(f'PV_L2_F6{module}.source' if original=='source' else original)+' '+args)
  else:
   sourceLines.append(line)
   if expr.startswith('lift ('):rec.append(f'  let {var} := {expr[6:-1]}')
   elif expr.startswith('Slice.index_usize '):
    arr,offset=expr.split()[1:];oid=0 if arr=='a' else 1
    val=f'({offset}).val' if '#' in offset else offset+'.val'
    rec.append(f'  let {var} ← operation (.index {oid} {val}) ({expr})')
   else:
    lhs,op,rhs=expr.split();ctor={'+':'add','*':'mul','%':'rem','-':'guard'}[op]
    lv=f'({lhs}).val' if '#' in lhs else lhs+'.val';rv=f'({rhs}).val' if '#' in rhs else rhs+'.val'
    event=f'.guard {num} {lv} {rv} true' if op=='-' else f'.{ctor} {lv} {rv}'
    rec.append(f'  let {var} ← operation ({event}) ({expr})')
 imports=''.join(f'import R1Z.PV_L2_F6{x}\n' for x in sorted({c[0] for c in callees.values()}))
 args=' '.join(' '.join(re.findall(r'\(([^:]+) :',params)).split())
 eq='R1CertCheck.mm x y' if mod=='MM' else 'source '+args
 erasures=','.join(f'PV_L2_F6{x[0]}.{x[3]}' for x in callees.values())
 middle=(erasures+',') if erasures else ''
 code=f'''import R1Z.PV_L2_RecordRefinement
{imports}
set_option autoImplicit false
namespace R1Z.PV_L2_F6{mod}
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def source {params} : Result ({result}) := do
{chr(10).join(sourceLines)}
def recorded {params} : Recorded ({result}) := do
{chr(10).join(rec)}
theorem erases {params} : (recorded {args}).value = {eq} := by
  simp only [recorded,{('R1CertCheck.mm' if mod=='MM' else 'source')},PV_L2_RecordCompact.bind_value,
    {middle}PV_L2_RecordCompact.operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6{mod}
'''
 if mod=='MM':
  code=code.replace('#print axioms erases', '''  cases (UScalar.cast .U64 x) * (UScalar.cast .U64 y) <;>
    simp only [bind_tc_fail,bind_tc_div,bind_tc_ok]
  rename_i value
  cases value % P <;> rfl
#print axioms erases''')
 emit(B/f'PV_L2_F6{mod}.lean',code)
print('checked' if CHECK else 'generated',len(rows),'half-check components')
