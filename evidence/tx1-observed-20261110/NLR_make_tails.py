from pathlib import Path
import re
P=Path(__file__).resolve().parent/'NLR_generated'
old=Path('evidence/tx1-prepare-20261110/NLJ_generated/NLJ_PrepareStep.lean').read_text()
# Literal phase parameters from the pinned NLJ phase-window signatures.
phases=['allocate','split','semanticRange','expandSemantic','valueRange','expandValues','rebuild','view','semantic','mapSemantic','mark','constructor']
params={};args={};body={}
for phase in phases:
 src=Path(f'evidence/tx1-prepare-20261110/NLJ_generated/NLJ_PrepareWindow_{phase}.lean').read_text()
 signature=src.split(' : Code (Post H) := do')[0].split('def window_'+phase)[1]
 signature=signature.replace('(s : State H)','(i : Input H)')
 params[phase]=signature
 m=re.search(r'\(atSite : s.locals = \.'+phase+r'(.*?)\) :',src,re.S)
 args[phase]=m.group(1).strip()
 body[phase]=src.split(' : Code (Post H) := do\n',1)[1].split('\ntheorem step_',1)[0].replace(' let i := s.input\n','')
header='''import NLJ_PrepareGoal
import NLJ_Monad
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareTails
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
'''
for phase in reversed(phases):
 b=body[phase]
 b=re.sub(r'pure \(\.inr \(advance s \.(\w+) (.*?)\)\)',lambda m:'tail_'+m[1]+' cfg i '+m[2],b)
 b=re.sub(r'pure \(\.inl (.*?)\)',r'pure \1',b)
 # Nested tuples .inl(...): remove only wrapping inl, preserve tuple syntax.
 b=body[phase]
 for nextphase in phases:
  b=re.sub(r'pure \(\.inr \(advance s \(\.'+nextphase+r' (.*?)\)\)\)',lambda m:'tail_'+nextphase+' cfg i '+m[1],b)
 b=b.replace('pure (.inl (','pure (')
 b=b.replace('pure (.inl out)','pure out')
 # removed outer wrapping paren in pure (.inl (...))
 b='\n'.join(line[:-1] if 'pure (' in line and line.endswith('))') and '.inl' not in line else line for line in b.splitlines())
 header+='def tail_'+phase+params[phase]+' : Code Out := do\n'+b+'\n\n'
header+='end AspisR1.NLR_PrepareTails\nend\n'
(P/'NLR_PrepareTails.lean').write_text(header)
