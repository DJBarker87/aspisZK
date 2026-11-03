"""Check the taint function itself without executing the ELF inventory main."""
from pathlib import Path
import ast,json
p=Path(__file__).with_name('PV_L3A_audit.py');tree=ast.parse(p.read_text())
# Load only helpers and their imports/constants, excluding all top-level I/O.
allowed={'reg','operands','regs','analyze'}
body=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom)) or isinstance(n,ast.FunctionDef) and n.name in allowed or isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='R' for t in n.targets)]
ns={};exec(compile(ast.Module(body=body,type_ignores=[]),str(p),'exec'),ns)
def scan(ops):
    return ns['analyze'](dict(names=['<aspis_core::field::M31>::inv'],instructions=[dict(address=hex(j),op=op,args=args,text=f'{j:x}: {op} {args}') for j,(op,args) in enumerate(ops)]))
cases={
 'secret_branch':([('test','%edi,%edi'),('je','3 <end>'),('ret',''),('ret','')], 'tainted conditional branch'),
 'secret_address':([('mov','(%rdi),%eax'),('ret','')], 'tainted memory address'),
 'secret_indirect':([('jmp','*%rdi')], 'tainted indirect target/address'),
 'secret_division':([('div','%edi'),('ret','')], 'tainted operand to latency-review instruction'),
 'alias_branch':([('mov','%edi,%eax'),('test','%al,%al'),('jne','3 <end>'),('ret','')], 'tainted conditional branch'),
}
results={}
for name,(ops,reason) in cases.items():
    r=scan(ops);assert any(a['reason']==reason for a in r['alerts']),(name,r);results[name]=True
r=scan([('mov','%edi,%eax'),('imul','%eax,%eax'),('ret','')]);assert r['classification']=='CLEAN',r;results['straight_arithmetic']=True
r=scan([('mystery','%edi,%eax'),('ret','')]);assert r['classification']=='UNRESOLVED',r;results['unsupported_fails_closed']=True
Path(__file__).with_name('controls.json').write_text(json.dumps(results,indent=2)+'\n');print(results)
