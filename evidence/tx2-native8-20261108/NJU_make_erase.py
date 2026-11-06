from pathlib import Path
import re
E=Path(__file__).resolve().parent;s=(E/'NJU_ResumeObserved.lean').read_text()
names=['finishTail','queryEnd','queryMid','queryBlock','resumeBody','header']
records=['recordRaw','recordK','recordE','recordSemantic','recordWeights','recordValidate','recordFilled','recordAny','recordDigest']
lemmas=['NJU_Log.erase_bind','NJU_Log.erase_record','NJU_Log.erase_lift','NJU_Log.erase_liftM','NJU_Log.erase_pure','NJU_Log.erase_if','NJU_Log.erase_flow','NJU_Log.prod_cases']
text='''import NJU_ResumeObserved
set_option autoImplicit false
noncomputable section
namespace NJU_ResumeErase
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
'''
done=[]
for name in names:
 g=name+'G' if name!='header' else 'run';r=name+'R' if name!='header' else 'runRef'
 start=s.index('def '+g+' ');body=s[start+len('def '+g+' '):]
 end=re.search(r':\s*NJU_Log.Run Event',body).start();params=body[:end].rstrip()
 groups=re.findall(r'\(([a-zA-Z0-9_ ]+)\s*:',params);args=' '.join(' '.join(x.split()) for x in groups)
 simpl=records+lemmas+done
 text+='\ntheorem '+name+' '+params+' :\n ('+g+' '+args+').result='+r+' '+args+' := by\n'
 text+=' simp only ['+','.join([g,r]+simpl)+']\n'
 text+=" repeat' first\n | (intro hypothesis)\n | rfl\n | (apply NIL_ResultCases.bind_congr; intro value)\n"
 text+=' | (fail_if_no_progress simp_all ['+','.join(simpl)+'])\n | split\n | rfl\n'
 text+=' all_goals simp_all only ['+','.join(simpl)+']\n'
 done.append(name)
text+='\n'+''.join('#print axioms '+name+'\n' for name in done)+'end NJU_ResumeErase\n'
a=text.index(' := by\n',text.index('theorem queryEnd'));b=text.index('\ntheorem queryMid',a)
text=text[:a]+' := by\n unfold queryEndG queryEndR\n simp only [NJU_Log.erase_bind,NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_record,NJU_Log.erase_pure,recordRaw,lift,bind_tc_ok]\n apply NIL_ResultCases.bind_congr\n rintro ⟨a21,r29⟩\n simp only [NJU_Log.erase_bind,NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_record,NJU_Log.erase_pure,recordRaw,lift,bind_tc_ok]\n apply NIL_ResultCases.bind_congr\n rintro ⟨a22,r30⟩\n simp only [NJU_Log.erase_bind,NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_record,NJU_Log.erase_pure,recordRaw,lift,bind_tc_ok]\n apply NIL_ResultCases.bind_congr\n rintro ⟨a23,r31⟩\n simp only [NJU_Log.erase_bind,NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_record,NJU_Log.erase_pure,recordRaw,lift,bind_tc_ok]\n apply NIL_ResultCases.bind_congr\n rintro ⟨a24,r32⟩\n simp only [NJU_Log.erase_bind,NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_record,NJU_Log.erase_pure,recordRaw,lift,bind_tc_ok]\n apply NIL_ResultCases.bind_congr\n rintro ⟨a25,r33⟩\n simp only [NJU_Log.erase_bind,NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_record,NJU_Log.erase_pure,recordRaw,lift,bind_tc_ok]\n apply NIL_ResultCases.bind_congr\n rintro ⟨a26,r34⟩\n simp only [NJU_Log.erase_bind,NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_record,NJU_Log.erase_pure,recordRaw,lift,bind_tc_ok,recordValidate]\n apply NIL_ResultCases.bind_congr\n intro validation\n apply NIL_ResultCases.bind_congr\n intro flow\n cases flow with\n | Break residual => rfl\n | Continue unit =>\n  cases unit\n  exact finishTail reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 (Array.make 22#usize [i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,core.num.U32.from_le_bytes a21,core.num.U32.from_le_bytes a22,core.num.U32.from_le_bytes a23,core.num.U32.from_le_bytes a24,core.num.U32.from_le_bytes a25,core.num.U32.from_le_bytes a26]) r34\n\n'+text[b:]
(E/'NJU_ResumeErase.lean').write_text(text)
