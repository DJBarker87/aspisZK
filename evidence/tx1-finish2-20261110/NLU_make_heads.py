from pathlib import Path
import re,hashlib,json,textwrap
E=Path(__file__).resolve().parent;D=E/'NLU_generated';source=E.parent/'tx1-driver2-20261109/NLC_generated/NLC_FinishStep.lean'
s=source.read_text();body=s[s.index(' match s.next with\n')+len(' match s.next with\n'):s.index('\nend AspisR1.NLC_Finish')]
parts=re.split(r'^ \| (.+?) =>\n?',body,flags=re.M);rows=[]
for labels,code in zip(parts[1::2],parts[2::2]):
 for label in labels.split(' | '):
  name=label.strip().removeprefix('.')
  text='import NLU_Execute\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.NLU_Heads\nopen Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish\nopen PreparedHashCode (Code)\n/-- Exact source occurrence, with SAME immutable inputs and local slots.\nThis is a source/G step, not a native producer or child-domain premise. -/\ndef head_NAME {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do\n let i:=s.input\n let l:=s.locals\nBODY\ntheorem source_NAME {H : Type} (s : NLU.State H) (atSite : s.machine.next=.NAME) :\n NLU.step s=NLU.execute s (head_NAME s.machine) := by\n rw [NLU.execute_step]\n have same : NLC_Finish.step s.machine=head_NAME s.machine := by\n  simp only [NLC_Finish.step,atSite]\n  rfl\n rw [same]\n#print axioms source_NAME\nend AspisR1.NLU_Heads\nend\n'.replace('NAME',name).replace('BODY',textwrap.indent(textwrap.dedent(code.rstrip()),' '))
  (D/f'NLU_Head_{name}.lean').write_text(text);rows.append(name)
(E/'NLU_HEAD_INPUT.json').write_text(json.dumps(dict(source=str(source.relative_to(E.parent.parent)),sha256=hashlib.sha256(source.read_bytes()).hexdigest(),occurrences=rows),indent=1))
print('Generated '+str(len(rows))+' exact parent occurrence source heads')
