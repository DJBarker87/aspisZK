from pathlib import Path
import re
E=Path(__file__).resolve().parent
s=Path('evidence/tx2-native8-20261108/NJU_ResumeObserved.lean').read_text()
names=['finishTail','queryEnd','queryMid','queryBlock','resumeBody','run']
prev='NKK_Clauses';done=[]
for ix,name in enumerate(names):
 g=name+'G' if name!='run' else 'run'
 block=s[s.index('def '+g+' ')+len('def '+g+' '):]
 params=block[:re.search(r':\s*NJU_Log.Run Event',block).start()].rstrip()
 # hash is absent in tails, but predicate must carry the same abstract digest receiver.
 if name!='run':params+=' (hash : H)'
 args=' '.join(' '.join(x.split()) for x in re.findall(r'\(([a-zA-Z0-9_ ]+)\s*:',params))
 callargs=args if name=='run' else args.removesuffix(' hash')
 module='NKK_Clauses'+name[0].upper()+name[1:]
 text=f'''import {prev}
set_option autoImplicit false
noncomputable section
namespace NKK_ResumeClauses
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

theorem {name} {params} :
 NKK_LogClauses.Holds (NKK_Clauses.Clause reservation d hash) ({g} {callargs}) := by
 unfold {g}
 repeat' first
'''
 for dn in reversed(done):text+=f' | (apply {dn})\n'
 for lemma in ['raw','k','e','semantic','weights','validate','filled','headerAny','digest']:
  text+=f' | (apply NKK_Clauses.{lemma})\n'
 text+=''' | (apply NKK_LogClauses.pure)
 | (apply NKK_LogClauses.lift)
 | (apply NKK_LogClauses.liftM)
 | (apply NKK_LogClauses.bind)
 | (apply NKK_LogClauses.branch)
 | (apply NKK_LogClauses.flow)
 | (intro value)
 | split
 | (cases_type Unit)
'''
 text+=f'\n#print axioms {name}\nend NKK_ResumeClauses\n'
 E.joinpath(module+'.lean').write_text(text)
 prev=module;done.append(name)
