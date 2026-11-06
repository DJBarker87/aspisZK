"""Generate explicit source-morphism goals for the pinned outlined caller bodies."""
from pathlib import Path
import re
E=Path(__file__).resolve().parent;source=(E.parent/'tx2-native8-20261108/NJU_ResumeObserved.lean').read_text()
laws='NKE_Free.eval_bind,NKE_Free.eval_record,NKE_Free.eval_liftM,NKE_Free.eval_pure,NKE_Free.eval_if,NKE_Free.eval_flow,NJU_Log.prod_cases'
common=['resume','powers','inactive','merkle','geometry','pending','query','flush','finish']
s='''import NKE_CommonProgram
import NKE_FreeReplay
set_option autoImplicit false
noncomputable section
namespace NKE_CommonEval
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NKE_Free.eval (NKE_CommonProgram.run wr rr merkle finish d pub proof ck hash none)=
 NJU_CommonObserved.run wr rr merkle finish d pub proof ck hash none := by
 simp only [NKE_CommonProgram.run,NJU_CommonObserved.run,LAWS,CODECS]
#print axioms source
end NKE_CommonEval
'''.replace('LAWS',laws).replace('CODECS',','.join('NKE_CommonCodec.'+n for n in common))
s=s.replace('import NKE_CommonProgram','import NKE_CommonProgram\nimport NKE_RunTactic')
line=next(l for l in s.splitlines() if l.startswith(' simp only ['))
s=s.replace(line,line+"\n repeat' first\n | nke_run_bind\n | nke_intro\n | (fail_if_no_progress"+line.replace(' simp only [',' simp_all only [')+")\n | split")
(E/'NKE_CommonEval.lean').write_text(s)
wrappers=['Raw','K','E','Semantic','Weights','Validate','Filled','Any','Digest'];codecs=['raw','k','e','semantic','weights','validate','filled','headerAny','digest']
prev=None
for i,name in enumerate(['finishTailG','queryEndG','queryMidG','queryBlockG','resumeBodyG','run'],1):
 start=source.index('def '+name+' ');ret=source.index('NJU_Log.Run Event',start);colon=source.rfind(':',start,ret);signature=source[start+len('def '+name):colon]
 args=[];depth=0;begin=None
 for j,ch in enumerate(signature):
  if ch in '({[':
   if depth==0:begin=j
   depth+=1
  elif ch in ')}]':
   depth-=1
   if depth==0 and signature[begin]=='(':
    args+=signature[begin+1:j].split(':',1)[0].split()
 names=' '.join(args)
 imports=['import NKE_ResumeProgram'+str(i),'import NKE_RunTactic']+(['import '+prev] if prev else ['import NKE_FreeReplay'])
 simp=[f'NKE_ResumeProgram.{name}',f'NJU_ResumeObserved.{name}',laws]
 for wrapper in wrappers:simp += ['NKE_ResumeProgram.record'+wrapper,'NJU_ResumeObserved.record'+wrapper]
 simp += ['NKE_ResumeCodec.'+n for n in codecs]
 if i>1:simp += ['NKE_ResumeEval.'+n for n in ['finishTailG','queryEndG','queryMidG','queryBlockG','resumeBodyG'][:i-1]]
 module='NKE_ResumeEval'+str(i)
 lines=imports+['set_option autoImplicit false','noncomputable section','namespace NKE_ResumeEval','open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved',f'theorem {name} {signature} :',f' NKE_Free.eval (NKE_ResumeProgram.{name} {names})=',f' NJU_ResumeObserved.{name} {names} := by',' simp only ['+','.join(simp)+']',f'#print axioms {name}','end NKE_ResumeEval','']
 text='\n'.join(lines)
 line=next(l for l in text.splitlines() if l.startswith(' simp only ['))
 text=text.replace(line,line+"\n repeat' first\n | nke_run_bind\n | nke_intro\n | (fail_if_no_progress"+line.replace(' simp only [',' simp_all only [')+")\n | split")
 (E/(module+'.lean')).write_text(text);prev=module
