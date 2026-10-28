"""Syntax-only reification of three pinned frozen control-flow bodies.
No source expression is evaluated by this script. Native adequacy is separate.
"""
from pathlib import Path
import hashlib,json,re,sys,subprocess
from proof_tree import proof
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
b=subprocess.check_output(['git','show','HEAD:'+p],cwd=R);s=b.decode()
assert (R/p).read_bytes()==b
stem='aspis_prover.state_only_entropy.'
names=[stem+'sync_directory',stem+'DurableStateOnlyMaskNonceStore.reserve_fallible',stem+'DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve']
short=['syncDirectory','reserveFallible','reserve']
headers=['(directory : std.path.Path) : P (core.result.Result Unit std.io.error.Error)', '(self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)\n  (statement_digest mask_nonce : Array Aeneas.Std.U8 32#usize) :\n  P ((core.result.Result Bool std.io.error.Error) × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)', '(self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)\n  (statement_digest mask_nonce : Array Aeneas.Std.U8 32#usize) :\n  P (Bool × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)']
entry='--entry' in sys.argv
entryargs='(public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)\n  (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)\n  (variant : transport.Variant)\n  (hash : Slice (Slice U8) → Aeneas.Std.Result (Array U8 32#usize))\n  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)\n  (nonce_store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)'
if entry:
 names=['prover.prove_masked_attempt'];short=['maskedAttempt']
 headers=[entryargs+' :\n  P ((core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error) × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)']
output=['import R1Z.PV_W_SourceSyntax\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_W_Reservation\nopen ProverRwFull PV_W_SourceSyntax PV_W_Syntax PV_W_Threading\nopen Aeneas.Std\nvariable [ExternalTypes]\n']
typed='--typed' in sys.argv or entry
constructors={'std.fs.File.open':'fileOpen','std.fs.File.sync_all':'fileSync','std.fs.OpenOptions.open':'optionsOpen','std.io.error.Error.kind':'errorKind','std.fs.File.Insts.StdIoWrite.write_all':'writeAll'}
if typed:
 output=[output[0].replace('PV_W_SourceSyntax','PV_W_TypedEffects').replace('namespace R1Z.PV_W_Reservation','namespace R1Z.PV_W_TypedReservation')+'open PV_W_SourceSyntax (source_bind_congr)\n']
if entry:output=[output[0].replace('PV_W_TypedReservation','PV_W_ProverEntry').replace('open Aeneas.Std\n','open Aeneas Aeneas.Std\n')]
rows=[];proofs={}
for name,new,header in zip(names,short,headers):
 mat=re.search(r'\ndef\s+'+re.escape(name)+r'\s*\(',s);assert mat,name
 start=s.index(':= do',mat.end())+len(':= do\n');end=s.index('\n\n',start);body=s[start:end]
 lines=[]
 for line in body.splitlines():
  if '=> ' in line and line.lstrip().startswith('| '):
   left,right=line.split('=> ',1);lines.extend([left+'=>',' '*(len(line)-len(line.lstrip())+2)+right])
  else:lines.append(line)
 proofs[new]=proof(lines,names,short,constructors if typed else ())
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
  if typed and label in constructors:
   args=expr[len(label):].strip()
   if label in ['std.fs.File.open','std.fs.OpenOptions.open']:
    if args.startswith('('):
     depth=0;cut=0
     for cut,ch in enumerate(args):
      if ch=='(':depth+=1
      elif ch==')':
       depth-=1
       if depth==0:cut+=1;break
    else:cut=len(args.split()[0])
    convert=args[:cut];rest=args[cut:].strip()
    args='(fun dictionary => letI : ExternalFuns := dictionary; '+convert+') '+rest
   es=args.splitlines();out.append(indent+prefix+'perform (.'+constructors[label]+' '+es[0]);out.extend(indent+'  '+v for v in es[1:]);out[-1]+=')';continue
  out.append(indent+prefix+'invoke '+json.dumps(label)+' (fun ops =>')
  out.append(indent+'  letI : ExternalFuns := ops')
  for el in expr.splitlines():out.append(indent+'  '+el)
  out[-1]+=')'
 output+=['/-- Generated syntax; helpers retain unexecuted source-call thunks. -/\ndef '+new+'\n  '+header+' := do\n'+'\n'.join(out)+'\n']
 rows.append(dict(name=name,body_sha256=hashlib.sha256(body.encode()).hexdigest(),calls=calls,generated=new))
if not entry:
 proofheaders=[
 '(ops : ExternalFuns) (directory : std.path.Path) :\n    erase ops (syncDirectory directory) =\n      @'+names[0]+' _ ops directory',
 '(ops : ExternalFuns) (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)\n    (statement_digest mask_nonce : Array U8 32#usize) :\n    erase ops (reserveFallible self statement_digest mask_nonce) =\n      @'+names[1]+' _ ops self statement_digest mask_nonce',
 '(ops : ExternalFuns) (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)\n    (statement_digest mask_nonce : Array U8 32#usize) :\n    erase ops (reserve self statement_digest mask_nonce) =\n      @'+names[2]+' _ ops self statement_digest mask_nonce']
else:
 proofheaders=['(ops : ExternalFuns) '+entryargs+' :\n    erase ops (maskedAttempt public1 compiled variant hash attempt nonce_store) =\n      @prover.prove_masked_attempt _ ops public1 compiled variant hash attempt nonce_store']
for old,new,h in zip(names,short,proofheaders):
 output.append('theorem erase_'+new+' '+h+' := by\n  unfold '+new+' '+old+'\n'+proofs[new]+'\n\n#print axioms erase_'+new+'\n')
output.append('end R1Z.'+('PV_W_ProverEntry' if entry else 'PV_W_TypedReservation' if typed else 'PV_W_Reservation')+'\n')
target=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/('PV_W_ProverEntry.lean' if entry else 'PV_W_TypedReservation.lean' if typed else 'PV_W_Reservation.lean');data='\n'.join(output)
if '--check' in sys.argv:assert target.read_text()==data
else:target.write_text(data)
(E/('entry-reification.json' if entry else 'typed-reservation-reification.json' if typed else 'reservation-reification.json')).write_text(json.dumps(dict(source_path=p,source_sha256=hashlib.sha256(b).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],cwd=R,text=True).strip(),bodies=rows,check=True,scope='control-flow reification and exact source erasure; native effect adequacy not asserted'),indent=2)+'\n')
print('Exact reification check:',len(rows),'bodies;',sum(len(x['calls']) for x in rows),'call sites')
