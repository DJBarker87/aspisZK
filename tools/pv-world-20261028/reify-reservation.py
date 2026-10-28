"""Syntax-only reification of three pinned frozen control-flow bodies.
No source expression is evaluated by this script. Native adequacy is separate.
"""
from pathlib import Path
import hashlib,json,re,sys,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
b=subprocess.check_output(['git','show','HEAD:'+p],cwd=R);s=b.decode()
assert (R/p).read_bytes()==b
stem='aspis_prover.state_only_entropy.'
names=[stem+'sync_directory',stem+'DurableStateOnlyMaskNonceStore.reserve_fallible',stem+'DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve']
short=['syncDirectory','reserveFallible','reserve']
headers=['(directory : std.path.Path) : P (core.result.Result Unit std.io.error.Error)', '(self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)\n  (statement_digest mask_nonce : Array Aeneas.Std.U8 32#usize) :\n  P ((core.result.Result Bool std.io.error.Error) × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)', '(self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)\n  (statement_digest mask_nonce : Array Aeneas.Std.U8 32#usize) :\n  P (Bool × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)']
output=['import R1Z.PV_W_SourceSyntax\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_W_Reservation\nopen ProverRwFull PV_W_SourceSyntax PV_W_Syntax PV_W_Threading\nopen Aeneas.Std\nvariable [ExternalTypes]\n']
rows=[]
for name,new,header in zip(names,short,headers):
 mat=re.search(r'\ndef\s+'+re.escape(name)+r'\s*\(',s);assert mat,name
 start=s.index(':= do',mat.end())+len(':= do\n');end=s.index('\n\n',start);body=s[start:end]
 lines=[]
 for line in body.splitlines():
  if '=> ' in line and line.lstrip().startswith('| '):
   left,right=line.split('=> ',1);lines.extend([left+'=>',' '*(len(line)-len(line.lstrip())+2)+right])
  else:lines.append(line)
 out=[];calls=[];i=0
 while i<len(lines):
  line=lines[i];m=re.match(r'^(\s*)let (.*?) ←(.*)$',line)
  if not m:
   if not line.strip() or line.lstrip().startswith(('let ','match ','| ','ok ','pure ')):
    out.append(re.sub(r'^(\s*)ok ',r'\1pure ',line));i+=1;continue
   indent=line[:len(line)-len(line.lstrip())];var=None;first=line.strip()
  else:indent,var,first=m.groups()
  parts=[first.strip()];i+=1
  while i<len(lines) and (not lines[i].strip() or len(lines[i])-len(lines[i].lstrip())>len(indent)):
   parts.append(lines[i].strip());i+=1
  expr='\n'.join(x for x in parts if x);calls.append(expr)
  expr=re.sub(r'\bok ', 'Aeneas.Std.Result.ok ',expr)
  inline=next(((old,n) for old,n in zip(names,short) if expr.startswith(old) and expr[len(old):len(old)+1].isspace()),None)
  prefix=('let '+var+' ← ') if var is not None else ''
  if inline:
   ls=expr.replace(inline[0],inline[1],1).splitlines();out.append(indent+prefix+ls[0]);out.extend(indent+'  '+v for v in ls[1:]);continue
  label=expr.split()[0]
  out.append(indent+prefix+'invoke '+json.dumps(label)+' (fun ops =>')
  out.append(indent+'  letI : ExternalFuns := ops')
  for el in expr.splitlines():out.append(indent+'  '+el)
  out[-1]+=')'
 output+=['/-- Generated syntax; helpers retain unexecuted source-call thunks. -/\ndef '+new+'\n  '+header+' := do\n'+'\n'.join(out)+'\n']
 rows.append(dict(name=name,body_sha256=hashlib.sha256(body.encode()).hexdigest(),calls=calls,generated=new))
output.append('''theorem erase_syncDirectory (ops : ExternalFuns) (directory : std.path.Path) :
    erase ops (syncDirectory directory) =
      @aspis_prover.state_only_entropy.sync_directory _ ops directory := by
  unfold syncDirectory aspis_prover.state_only_entropy.sync_directory
  repeat' (simp only [erase_bind,erase_invoke,erase_pure,erase_coreResult,erase_controlFlow,erase_ite]; first | rfl | apply congrArg (Aeneas.Std.bind _) | funext x | split)

theorem erase_reserveFallible (ops : ExternalFuns)
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) :
    erase ops (reserveFallible self statement nonce) =
      @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
        _ ops self statement nonce := by
  unfold reserveFallible aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  repeat' (simp only [erase_bind,erase_invoke,erase_pure,erase_coreResult,erase_controlFlow,erase_ite,erase_syncDirectory]; first | rfl | apply congrArg (Aeneas.Std.bind _) | funext x | split)

theorem erase_reserve (ops : ExternalFuns)
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) :
    erase ops (reserve self statement nonce) =
      @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
        _ ops self statement nonce := by
  unfold reserve aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  repeat' (simp only [erase_bind,erase_invoke,erase_pure,erase_coreResult,erase_controlFlow,erase_ite,erase_reserveFallible]; first | rfl | apply congrArg (Aeneas.Std.bind _) | funext x | split)

#print axioms erase_syncDirectory
#print axioms erase_reserveFallible
#print axioms erase_reserve
end R1Z.PV_W_Reservation
''')
target=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_W_Reservation.lean';data='\n'.join(output)
if '--check' in sys.argv:assert target.read_text()==data
else:target.write_text(data)
(E/'reservation-reification.json').write_text(json.dumps(dict(source_path=p,source_sha256=hashlib.sha256(b).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],cwd=R,text=True).strip(),bodies=rows,check=True,scope='control-flow reification and exact source erasure; native effect adequacy not asserted'),indent=2)+'\n')
print('Exact reification check:',len(rows),'bodies;',sum(len(x['calls']) for x in rows),'call sites')
