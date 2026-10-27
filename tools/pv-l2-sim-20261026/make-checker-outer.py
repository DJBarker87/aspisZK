"""Source-shaped outer checker loops. No native/certificate factoring claim."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
SRC=(B/'CertCheckExtracted.lean').read_text();CHECK='--check' in sys.argv
ROWS=[
 ('id_ok','Identity','c co w','i','w','ok1 && b','i1',{'id_row_ok':('IdentityRow','recorded','erases')}),
 ('ech_ok','Echelon','e n lst r','a','r','ok1 && b','a1',{'ech_row_ok':('EchelonRow','recorded','erases')}),
 ('nvec_ok','Null','nm e n lst tag r k','f','k','ok1 && b','f1',{'nvec_row_ok':('NullRow','recorded','erases')}),
 ('lifts_ok','Lifts','o u id lw loff nl','l','nl','(ok1 && b0) && b1','l1',{
   'prod_ok':('Callers','product','product_erases'),'id_ok':('Identity','recorded','erases')}),
 ('ents_ok','Entries','ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero','e','m',
  '(((ok1 && b0) && b1) && b2) && b3','e1',{
   'piv_ok':('Callers','piv','piv_erases'),'kimg_ok':('Callers','image','image_erases')}),
]
def emit(path,text):
 if CHECK:
  if not path.exists() or path.read_text()!=text:raise SystemExit('stale '+str(path))
 else:path.write_text(text)
for number,(fn,mod,args,index,bound,flag,inc,callees) in enumerate(ROWS,20):
 start=SRC.index('def '+fn+'_loop\n');end=SRC.index('partial_fixpoint',start)
 header,body=SRC[start:end].split('  := do\n',1)
 params=header[header.index('\n'):header.index(' :\n  Result')]
 fixed=params[:params.index('(ok1 : Bool)')].rstrip()
 seq=body.split('  then\n',1)[1].split('    '+fn+'_loop',1)[0]
 lines=seq.splitlines();rec=[];binds=[]
 for line in lines:
  m=re.fullmatch(r'    let (\w+) ← (.*)',line)
  if not m:raise ValueError(line)
  var,expr=m.groups();binds.append(var);op=expr.split()[0]
  if op in callees:
   module,record,_=callees[op];rec.append('  let '+var+' ← PV_L2_F6'+module+'.'+record+' '+expr.split(' ',1)[1])
  elif expr.startswith('lift ('):rec.append(f'  let {var} := {expr[6:-1]}')
  elif expr.startswith('Slice.index_usize '):
   arr,offset=expr.split()[1:];rec.append(f'  let {var} ← operation (.index {args.split().index(arr)} {offset}.val) ({expr})')
  else:
   lhs,op,rhs=expr.split();ctor={'+':'add','*':'mul'}[op]
   rv=f'({rhs}).val' if '#' in rhs else rhs+'.val'
   rec.append(f'  let {var} ← operation (.{ctor} {lhs}.val {rv}) ({expr})')
 rec.append(f'  operation (.guard {number} 0 0 ({flag})) (ok ({flag},{inc}))')
 imports=''.join(f'import R1Z.PV_L2_F6{dep}\n' for dep in sorted({x[0] for x in callees.values()}))
 erasures=','.join('PV_L2_F6'+x[0]+'.'+x[2] for x in callees.values())
 pa=f'{fixed} (ok1 : Bool) ({index} : Usize)'
 code=f'''import R1Z.PV_L2_RecordCompact
import R1Z.PV_L2_F6FlagLoop
{imports}
set_option autoImplicit false
namespace R1Z.PV_L2_F6{mod}Step
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def step {pa} : Result (Bool × Usize) := do
{chr(10).join(x[2:] for x in lines)}
  ok ({flag},{inc})
def recorded {pa} : Recorded (Bool × Usize) := do
{chr(10).join(rec)}
theorem recorded_erases {pa} :
    (recorded {args} ok1 {index}).value = step {args} ok1 {index} := by
  simp only [recorded,step,PV_L2_RecordCompact.bind_value,
    {erasures},PV_L2_RecordCompact.operation_bind_value,
    operation_value,lift,bind_tc_ok]
theorem unroll {pa} :
    {fn}_loop {args} ok1 {index} = if {index}<{bound} then (do
      let (flag1,index1) ← step {args} ok1 {index}
      {fn}_loop {args} flag1 index1) else ok ok1 := by
  rw [{fn}_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl
theorem increment {pa} (after : Bool × Usize)
    (success : step {args} ok1 {index} = ok after) : after.2.val={index}.val+1 := by
  unfold step at success
'''
 for var in binds:code+=f'  obtain ⟨{var},h{var},success⟩ := bind_eq_ok success\n'
 code+=f'''  have he := ok_inj success
  rw [←he]
  simpa only [show (1#usize).val=1 from rfl] using add_ok h{inc}
#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6{mod}Step
'''
 emit(B/f'PV_L2_F6{mod}Step.lean',code)
 code=f'''import R1Z.PV_L2_F6{mod}Step
set_option autoImplicit false
namespace R1Z.PV_L2_F6{mod}
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
open R1Z.PV_L2_F6{mod}Step
def recorded {fixed} : Recorded Bool :=
  PV_L2_F6FlagLoop.loop {number} (PV_L2_F6{mod}Step.recorded {args}) {bound} {bound}.val true 0#usize
theorem erases {fixed} :
    (recorded {args}).value = {fn} {args} := by
  unfold recorded
  apply PV_L2_F6FlagLoop.erases {number} (PV_L2_F6{mod}Step.recorded {args}) {bound} ({fn}_loop {args})
  · intro flag index
    rw [recorded_erases]
    exact unroll {args} flag index
  · intro flag index after hs
    rw [recorded_erases] at hs
    exact increment {args} flag index after hs
  · omega
#print axioms erases
end R1Z.PV_L2_F6{mod}
'''
 emit(B/f'PV_L2_F6{mod}.lean',code)
print('checked' if CHECK else 'generated',len(ROWS)*2,'outer modules')
