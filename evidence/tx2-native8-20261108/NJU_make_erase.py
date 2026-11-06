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
(E/'NJU_ResumeErase.lean').write_text(text)
