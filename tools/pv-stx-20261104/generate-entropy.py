"""Syntax-directed lift of six pinned extraction definitions, with --check.
The five opaque calls become typed requests; finite ordinary library operations
remain Result nodes. This script does not certify native effect-freedom.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys
P='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
raw=subprocess.check_output(['git','show','fd4a644fd4:'+P]);src=raw.decode()
root='aspis_prover.state_only_entropy.'
names=[root+'entropy_nonzero32_loop.body',root+'entropy_nonzero32_loop',root+'entropy_nonzero32',root+'StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body',root+'StateOnlyAttemptSecrets.generate_for_mask_nonce_loop',root+'StateOnlyAttemptSecrets.generate_for_mask_nonce']
new=['nonzeroBody','nonzeroLoop','nonzero','entropyBody','entropyLoop','generate']
replace=dict(zip(names,new));opmap={
 'zeroize.Zeroizing.new':'new',
 'zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut':'asMut',
 'zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut':'derefMut',
 'zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref':'deref',
 'getrandom.fill':'fill'}
blocks=[];records=[];sites=[]
for old,n in zip(names,new):
 m=re.search(r'^def\s+'+re.escape(old)+r'(?=\s|\{|\()[\s\S]*?(?=\n/--|\Z)',src,re.M);assert m,old
 block=m[0].rstrip();sig,body=block.split(':= do',1)
 sig=sig.replace(old,n,1);sig=re.sub(r'(?<![A-Za-z0-9_.])Result\b','Code Request',sig,count=1)
 lines=body.splitlines();out=[];i=0
 while i<len(lines):
  line=lines[i];lm=re.match(r'^(\s*)let (.*?) ←(.*)$',line)
  if not lm:out.append(line);i+=1;continue
  indent,pat,tail=lm.groups();expr=[tail.strip()];i+=1
  while i<len(lines) and (not lines[i].strip() or len(lines[i])-len(lines[i].lstrip())>len(indent)):
   expr.append(lines[i].strip());i+=1
  exp='\n'.join(expr).strip();matched=False
  for callee,op in opmap.items():
   if exp.startswith(callee+' ' ) or exp.startswith(callee+'\n'):
    exp='Code.call (Request.'+op+exp[len(callee):]+')';matched=True;sites.append(dict(definition=old,kind='request',callee=callee));break
  if not matched:
   for callee,local in replace.items():
    if exp.startswith(callee+' ') or exp.startswith(callee+'\n'):
     exp=local+exp[len(callee):];matched=True;sites.append(dict(definition=old,kind='local source code',callee=callee));break
  if not matched:
   sites.append(dict(definition=old,kind='finite Result node: native effect audit remains',expression=exp))
   exp='Code.result ('+exp+')'
  out.append(indent+'let '+pat+' ←\n'+ '\n'.join(indent+'  '+l for l in exp.splitlines()))
 body='\n'.join(out)
 for oldname,newname in sorted(replace.items(),key=lambda p:-len(p[0])):
  body=body.replace(oldname,newname)
 body=re.sub(r'(?<![A-Za-z0-9_.])ok\b','pure',body)
 body=re.sub(r'(?m)^(\s*)loop\s*$',r'\1Code.loop',body)
 blocks.append(sig+':= do'+body+'\n')
 records.append(dict(source_name=old,lifted_name=n,source_span=[src[:m.start()].count('\n')+1,src[:m.end()].count('\n')+1],source_text_sha256=hashlib.sha256(m[0].encode()).hexdigest()))
head='''import PV_STX_Code
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_STX_Entropy
open Aeneas Aeneas.Std ProverRwFull ControlFlow
open PV_STX_Code
variable [ExternalTypes]

/-- The actual five opaque call points reached by the entropy source body.
Their arguments, mutable restoration functions, and source errors are retained.
No world reply is supplied at construction time. -/
inductive Request : Type → Type 1 where
  | new {Z : Type} (zi : zeroize.Zeroize Z) (value : Z) : Request (zeroize.Zeroizing Z)
  | asMut {T Z : Type} (inst : core.convert.AsMut Z T) (zi : zeroize.Zeroize Z)
      (value : zeroize.Zeroizing Z) : Request (T × (T → zeroize.Zeroizing Z))
  | derefMut {Z : Type} (zi : zeroize.Zeroize Z) (value : zeroize.Zeroizing Z) :
      Request (Z × (Z → zeroize.Zeroizing Z))
  | deref {Z : Type} (zi : zeroize.Zeroize Z) (value : zeroize.Zeroizing Z) : Request Z
  | fill (buffer : Slice U8) : Request ((core.result.Result Unit getrandom.error.Error) × Slice U8)

variable [ExternalFuns]
def fixed : {X : Type} → Request X → Result X
  | _, .new zi value => zeroize.Zeroizing.new zi value
  | _, .asMut inst zi value => zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut inst zi value
  | _, .derefMut zi value => zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut zi value
  | _, .deref zi value => zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zi value
  | _, .fill buffer => getrandom.fill buffer

'''
tail='''
/-- Symbolic erasure, not a native trace law. These equalities impose NO
fixed-answer condition on an advancing handler. -/
theorem nonzeroBody_erases (bytes : Array U8 32#usize) (combined : U8) (i : Usize) :
    denote fixed (nonzeroBody bytes combined i) =
      aspis_prover.state_only_entropy.entropy_nonzero32_loop.body bytes combined i := by
  rfl

theorem nonzeroLoop_erases (bytes : Array U8 32#usize) (combined : U8) (i : Usize) :
    denote fixed (nonzeroLoop bytes combined i) =
      aspis_prover.state_only_entropy.entropy_nonzero32_loop bytes combined i := by
  rfl

theorem nonzero_erases (bytes : Array U8 32#usize) :
    denote fixed (nonzero bytes) = aspis_prover.state_only_entropy.entropy_nonzero32 bytes := by
  rfl

theorem entropyBody_erases (nonce : Array U8 32#usize) (limit retry : Usize) :
    denote fixed (entropyBody nonce limit retry) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body nonce limit retry := by
  rfl

theorem entropyLoop_erases (nonce : Array U8 32#usize) (limit retry : Usize) :
    denote fixed (entropyLoop nonce limit retry) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop nonce limit retry := by
  rfl

theorem generate_erases (nonce : Array U8 32#usize) :
    denote fixed (generate nonce) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce := by
  rfl

#print axioms nonzeroBody_erases
#print axioms nonzeroLoop_erases
#print axioms nonzero_erases
#print axioms entropyBody_erases
#print axioms entropyLoop_erases
#print axioms generate_erases
end PV_STX_Entropy
'''
s=head+'\n'.join(blocks)+tail
p=Path('lean/PV_STX_Entropy.lean');manifest=dict(source_revision='fd4a644fd414079022f8781c14a6683b41504ab7',source_path=P,source_sha256=hashlib.sha256(raw).hexdigest(),definitions=records,sites=sites,output_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification='Source-code lifting and symbolic fixed erasure only. Native primitive interpretation, stack/thread resources, complete entry compilation and five projections remain unconstructed.')
e=Path('evidence/pv-stx-20261104/entropy-generation.json')
if '--check' in sys.argv:
 assert p.read_text()==s;assert json.loads(e.read_text())==manifest;print('PASS entropy syntax generation')
else:p.write_text(s);e.write_text(json.dumps(manifest,indent=2)+'\n')
