from pathlib import Path
import json,ast
E=Path(__file__).resolve().parent;D=E/'NLI_generated';plan=json.loads((E/'NLI_SUFFIX_PLAN.json').read_text())
A=next(ast.literal_eval(n.value) for n in ast.parse((E/'NLI_generate_suffixes.py').read_text()).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='A' for t in n.targets))
built={json.loads(p.read_text()).get('module') for p in E.glob('NLI_L*/receipt.json') if json.loads(p.read_text())['exit_status']==0}
for ev,bindings,reads,writes,kind in A:
 p=D/(plan[ev]['module']+'.lean')
 if p.stem in built or ev in ['mark2','mark3','original','alpha']:continue
 s=p.read_text();start=s.index('def suffix_');end=s.index('theorem ',start);d=s[start:end]
 live=plan[ev]['live'];nxt=plan[ev]['next'];n=plan[ev]['n']-1
 before={f:f for f in live};after={**before,**writes}
 rec='{l with '+', '.join(f'{f}:=some {v}' for f,v in after.items())+'}' if after else 'l'
 cont='fold n {input:=i,next:=.'+nxt+',locals:='+rec+'}'
 lines=d.splitlines()
 for j,line in enumerate(lines):
  if ('suffix_'+nxt+' i') in line:
   a=line.index('suffix_'+nxt+' i');lines[j]=line[:a]+cont
 d='\n'.join(lines)+'\n'
 d=d.replace('def suffix_'+ev,'def window_'+ev+' (n : Nat)').replace('(i : Input H)','(i : Input H) (l : Locals H)',1)
 # Use the source theorem's binders and original before-state, but abstract the fuel.
 t=s[s.index('theorem '):s.index(' := by\n',s.index('theorem '))]
 t=t.replace('theorem '+ev,'theorem '+ev+'_head').replace('fold '+str(n+1),'fold (n+1)').replace('run (suffix_'+ev+' i','run (window_'+ev+' n i l')
 t=t.replace('{H : Type}','(n : Nat) {H : Type}',1)
 proof=' rw [fold]\n simp only [step,NLC_Finish.read]\n unfold window_'+ev+'\n try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]\n'
 for binding in bindings:
  proof+=' apply NLI_Notation.congr_bind\n'
  if kind=='resultPair':proof+=' rintro ⟨r,t1⟩\n'
  else:
   var=binding.split(' ←')[0].replace('let ','') if binding.startswith('let ') else 'ignored'
   proof+=' intro '+var+'\n'
  proof+=' try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]\n'
 if kind.startswith('result'):proof+=' cases r <;> rfl\n'
 elif kind=='plain':proof+=' rfl\n'
 else:proof+=' cases reject <;> rfl\n'
 head='''import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
'''
 (D/('NLI_Window_'+ev+'.lean')).write_text(head+d+t+' := by\n'+proof+'#print axioms '+ev+'_head\nend AspisR1.NLI_Window\nend\n')
 # Replace the failed concrete normalization with the generic head theorem.
 s=s.replace('import NLI_MonadNotation','import NLI_MonadNotation\nimport NLI_Window_'+ev)
 a=s.index(' := by\n',s.index('theorem'))+len(' := by\n');b=s.index(' apply NLI_Notation.congr_bind',a) if bindings else -1
 if b!=-1:
  prefix=' rw [NLI_Window.'+ev+'_head '+str(n)+']\n unfold NLI_Window.window_'+ev+' suffix_'+ev+'\n try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]\n'
  s=s[:a]+prefix+s[b:]
 p.write_text(s)
print('Split uncompiled concrete suffixes into abstract-fuel head and chain modules')
