from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RunJoin_NativeParametric55.lean').read_text();a=s.index('\n  {T0 : Type}');z=s.index(' :\n    Rel',a);binders=s[a:z]
out='''import R1Z.PV_RunJoin_NativeAuditContext55
import R1Z.PV_RunJoin_NativeAfterAuditRel55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAuditRel55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
open PV_RunJoin_ResultRelation55 PV_RunJoin_NativeResult55
variable [ExternalTypes] [ExternalFuns]
theorem complete {A B : Type} (R : A → B → Prop)
    (f : Phase → Result (core.result.Result A verifier.Error))
    (g : Phase → Result (core.result.Result B verifier.Error))
    (step : ∀ p,Rel (CoreRel R) (f p) (g p))'''+binders+''' :
    Rel (Output R)
      (PV_RunJoin_NativeAuditContext55.run f aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash context binding attempt nonce_store)
      (PV_RunJoin_NativeAuditContext55.run g aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash context binding attempt nonce_store) := by
  unfold PV_RunJoin_NativeAuditContext55.run
'''
lines=[];indent='  '
def emit(s):lines.append(indent+s)
def bind(n):emit('apply PV_RunJoin_ResultRelation55.same_bind');emit('intro '+n)
def pair(n):bind(n);emit('dsimp only [Aeneas.Std.uncurry]')
def case(n,v):
 global indent
 emit('cases '+n+' with');emit('| Err e => exact PV_RunJoin_NativeResult55.error R _ _');emit('| Ok '+v+' =>');indent+='  ';emit('simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]')
def reject(cond,name,continueTrue=False):
 global indent
 emit('by_cases '+name+' : '+cond)
 if not continueTrue:
  emit('· simp only [if_pos '+name+']');emit('  exact PV_RunJoin_NativeResult55.error R _ _');emit('· simp only [if_neg '+name+']');indent+='  '
 else:
  emit('· simp only [if_neg '+name+']') if False else None
  # Put the false branch first to keep the successful branch last.
  lines[-1]=indent+'by_cases '+name+' : ¬('+cond+')'
  emit('· simp only [if_neg '+name+']');emit('  exact PV_RunJoin_NativeResult55.error R _ _');emit('· have '+name+'good : '+cond+' := Classical.not_not.mp '+name);emit('  simp only [if_pos '+name+'good]');indent+='  '
pair('reservation');bind('maskStatus');case('maskStatus','maskPair');bind('cloned');pair('applied');bind('appliedStatus');case('appliedStatus','masks');bind('activeResult');bind('activeStatus');case('activeStatus','active');bind('dResult');bind('dStatus');case('dStatus','dvec');bind('arrayResult');bind('arrayStatus');case('arrayStatus','d')
reject('(alloc.vec.Vec.len masks.g != 1024#usize)=true','glen')
reject('(alloc.vec.Vec.len masks.h1_padding != 1024#usize)=true','plen')
bind('gcol');bind('padding');emit('simp only [lift,bind_tc_ok]');bind('audit')
reject('(audit.c1_columns_inactive_balanced != 16#usize)=true','c1count')
reject('(audit.mask_only_columns_inactive_balanced != 10#usize)=true','maskcount')
for field in ['d_inactive_balanced','g_inactive_balanced','h1_padding_inactive_balanced']:reject('audit.'+field+'=true',field,True)
emit('apply PV_RunJoin_NativeAfterAuditRel55.complete R f g step')
out+='\n'.join(lines)+'\n#print axioms complete\nend R1Z.PV_RunJoin_NativeAuditRel55\n';(L/'PV_RunJoin_NativeAuditRel55.lean').write_text(out)
