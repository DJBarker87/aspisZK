from pathlib import Path
E=Path(__file__).resolve().parent
header='''import NJB_Cuts
import NJB_ActiveRawLow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_LowDischarge
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
def operation (kind : Nat) (a b : NQ) : Result NQ :=
 if kind=0 then FIq_Native.field.QM31.mul a b else FIq_Native.field.QM31.add a b
/-- Complete entered child Results for the exact K020..033 operand trace.
Every clause is discharged below; no clause is an input hypothesis. -/
def Clauses (high : Fin 7 → NQ) (low : Fin 16 → NQ) (sum : NQ)
 (r : Fin 17 → NQ) (c : Fin 7) : Prop :=
 ∀ j : Fin (NJB_Cuts.lowCount c+1),
 operation (if j.val=NJB_Cuts.lowCount c-1 then 0 else 1)
  (NJB_Cuts.lowLeft high low sum r c j) (NJB_Cuts.lowRight low r c j)=ok (r ⟨j.val,by have := NJB_Cuts.low_count_bound c;omega⟩)
/-- Universal-reply native cut instantiated at the SAME canonical emitted
child Results. K020/021 through K032/033; full unused reply domain is met
by canonical ZERO, not assumed. The cut's exact final reply is consumed. -/
theorem source (high : Fin 7 → NQ) (low : Fin 16 → NQ) (sum : NQ) (c : Fin 7)
 (hh : ∀ i,Canon (high i)) (hl : ∀ i,Canon (low i)) (hs : Canon sum) :
 ∃ r : Fin 17 → NQ, (∀ j,Canon (r j)) ∧ Clauses high low sum r c ∧
 ∀ events calls next out,
 NJB_Cuts.low high low sum r c events calls next out →
 NJB_ActiveRawLow.step high low sum c=ok out := by
 fin_cases c
'''
indices=[[11,12],[0,11,12],[0,12],[11],[0,11],[1,2,5,6,9,10,13,14],[0,2,4,6,7,9,10]]
parts=[header]
for c,idx in enumerate(indices):
 lines=[' ·'];names=[];can=[];calls=[];prev=f'low {idx[0]}';cp='hl _'
 for i,k in enumerate(idx[1:]):
  q=f'q{i}';lines += [f'   obtain ⟨{q},h{i},c{i},_⟩ := NJB_StubLaws.qm_add ({prev}) (low {k}) ({cp}) (hl _)'];names.append(q);can.append(f'c{i}');calls.append(f'h{i}');prev=q;cp=f'c{i}'
 lines += [f'   obtain ⟨p,hp,cp,_⟩ := NJB_StubLaws.qm_mul (high {c}) ({prev}) (hh _) ({cp})', '   obtain ⟨v,hv,cv,_⟩ := NJB_StubLaws.qm_add sum p hs cp']
 names += ['p','v'];can+=['cp','cv'];calls+=['hp','hv'];n=len(names)
 vec=names+['FIq_Native.field.QM31.ZERO']*(17-n)
 lines += [f'   let r : Fin 17 → NQ := ![{",".join(vec)}]', '   refine ⟨r,?_,?_,?_⟩', '   · intro j; fin_cases j <;> dsimp only [r] <;> assumption_or_zero', '   · intro j; fin_cases j <;>', f'      simpa [Clauses,operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using_cases', '   · intro events calls next out cut', '     have ho := cut.2.2.2.2.2.2.1', f'     have same : out=v := by simpa [NJB_Cuts.lowCount,r] using ho', '     rw [same]', '     simp [NJB_ActiveRawLow.step,NJB_ActiveRawLow.lowSum,'+','.join(calls)+']']
 # Use first | exact to avoid tactic generators / broad reduction of recurrences.
 lines=[l.replace('assumption_or_zero','first | assumption | exact FIv_NativeValue.zero.1').replace('using_cases','using '+calls[0]) for l in lines]
 # Each entered j chooses the already-proved actual child equation.
 start=lines.index('   · intro j; fin_cases j <;>')
 lines[start:start+2]=['   · intro j; fin_cases j']+[f'     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using {h}' for h in calls]
 parts += ['\n'.join(lines)+'\n']
parts += ['#print source\n#print axioms source\nend AspisR1.NJL_LowDischarge\nend\n']
(E/'NJL_LowDischarge.lean').write_text(''.join(parts))
