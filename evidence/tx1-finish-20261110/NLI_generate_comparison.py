from pathlib import Path
E=Path(__file__).resolve().parent
s='''import NLI_Suffix_rounds
import NLI_LiftLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Source continuation comparison only. Child calls stay opaque; equations
for repeated pure getters are produced internally by congr_lift. -/
theorem suffix_eq_finish {H : Type} (i : Input H) :
 run (suffix_rounds i) = run (S1SemanticCode.finish NJM_RoundJoin.R
 (IDa_Deployed.boundaries i.reservation) i.digest i.publicValue i.prefix1
 i.transcript i.challenges none) := by
 rw [NKA_FinishTrace.source]
 unfold suffix_rounds
 apply NLI_Notation.congr_bind
 intro r
 cases r with
 | Err error => rfl
 | Ok value =>
  rcases value with ⟨running,alpha,transcript⟩
  unfold NKA_FinishTrace.afterRounds
'''
indent='  '
norm='try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]'
def emit(t):
 global s
 s+='\n'.join(indent+l if l else '' for l in t.splitlines())+'\n'
def plain(ev,var):
 emit('unfold suffix_'+ev);emit(norm)
 emit('apply NLI_LiftLaws.congr_lift');emit('intro '+var+' h_'+var)
def result(ev,var,eq=None):
 global indent
 emit('unfold suffix_'+ev);emit(norm)
 emit('apply NLI_LiftLaws.congr_lift');emit('intro r '+(eq or 'h_'+var))
 emit('cases r with\n| Err error => rfl\n| Ok '+var+' =>')
 indent+=' '
def mark(ev):
 emit('unfold suffix_'+ev)
 emit('simp only [VerifyPrefix.mark,NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]')
mark('mark2');result('claims','claims')
emit('unfold suffix_original')
plain('terminal','terminalReply');result('mapPublic','terminal')
mark('mark3');plain('lowArray','low');plain('highArray','high')
emit('unfold suffix_blind');emit(norm)
emit('apply NLI_LiftLaws.congr_lift\nintro row h_row\napply NLI_LiftLaws.congr_lift\nintro blind h_blind')
emit('unfold suffix_alpha');plain('mask','mask')
result('record25a','record25','h25');result('decode25','extra')
plain('multiply','product');plain('addMask','partialValue');plain('extra28','extraCell');plain('addExtra','masked')
plain('terminalGuard','reject');emit('cases reject with\n| true => rfl\n| false =>');indent+=' '
mark('mark4');plain('stateBefore','stateBefore')
emit('unfold suffix_record25b');emit('simp only [h25,NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]')
def circle(ev,var,tr):
 global indent
 emit('unfold suffix_'+ev);emit(norm)
 emit('apply NLI_Notation.congr_bind\nrintro ⟨r,'+tr+'⟩\ncases r with\n| Err error => rfl\n| Ok '+var+' =>');indent+=' '
circle('circle0','z0','transcript1')
result('record26a','record26','h26');result('decode26','beforeZ1')
emit('unfold suffix_record26b');emit('simp only [h26,NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]')
circle('circle1','z1','transcript2');mark('mark5');plain('circleGuard','reject1');emit('cases reject1 with\n| true => rfl\n| false =>');indent+=' '
result('payload2','payload')
emit('unfold suffix_rootCopy');emit(norm)
emit('apply NLI_LiftLaws.congr_lift\nintro rootResult h_rootResult\napply NLI_LiftLaws.congr_lift\nintro root h_root\nunfold tailVerified\nrfl')
s+='''#print axioms suffix_eq_finish
#print suffix_eq_finish
end AspisR1.NLI_Source
end
'''
(E/'NLI_generated/NLI_SourceComparison.lean').write_text(s)
print('source comparison generated; not yet compiled')
