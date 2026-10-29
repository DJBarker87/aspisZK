"""Emit named shallow continuation equations; no traversal through later stages."""
from pathlib import Path
import re,sys,json
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';raw=(L/'PV_B3P_P227_11.lean').read_text().split('  := do\n',1)[1].split('\n\n\nend ',1)[0];lines=raw.splitlines();starts=[0]+[i for i,l in enumerate(lines)if i and re.match(r'  let (?:i2|digests3|i4|block(?:[1-9][0-9]*)?|i46) (?:←|:=)',l)];chunks=['\n'.join(lines[a:b])for a,b in zip(starts,starts[1:]+[len(lines)])]
params='''(public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
header='''namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
'''
# Associativity is case analysis on only one Result tag; no field computation.
f=L/'PV_B3P_DigestAssoc227.lean';text='import PV_B3P_DigestFields227\n'+header+'''theorem digest_assoc {α β γ : Type} (r : Result α) (f : α → Result β) (g : β → Result γ) :
    (r >>= f) >>= g = r >>= (fun a => f a >>= g) := by
  cases r <;> rfl
#print axioms digest_assoc
end PV_B3P_Success227
'''
files={f.stem:text}
for i in reversed(range(25)):
 mod=f'PV_B3P_DigestSuffix{i:02}227';nextmod=f'PV_B3P_DigestSuffix{i+1:02}227';name=f'digest_suffix_{i:02}';ch=chunks[i]
 if i:ch=re.sub(r'\bdigests'+str(i)+r'\b','output',ch)
 if i<24:ch+=f'\n  digest_suffix_{i+1:02} public1 openings selectors digests{i+1}'
 ch=re.sub(r'\bok\b','Result.ok',ch)
 text=f'import PV_B3P_DigestStage{i:02}227\nimport PV_B3P_DigestAssoc227\n'+(f'import {nextmod}\n'if i<24 else '')+header
 text+=f'def {name} {params}'+(' (output : Digest8Q)'if i else '')+' : Result Digest8Q := do\n'+ch+'\n'
 # Keep callees and the next continuation opaque while checking one equation.
 opaque=['reference_terminal.add_digest_binding','reference_copy_terminal.Selectors.row','reference_terminal.empty_root','reference_terminal.digest227','reference_terminal.bounded_append_carry']+([f'digest_suffix_{i+1:02}']if i<24 else [])
 text+='\nattribute [local irreducible] '+' '.join(opaque)+'\n'
 args='public1 openings selectors'+(' output'if i else '')
 rhs=f'digest_stage_{i:02} '+args+(f' >>= digest_suffix_{i+1:02} public1 openings selectors'if i<24 else '')
 text+=f'\ntheorem {name}_equation {params}'+(' (output : Digest8Q)'if i else '')+f' :\n    {name} {args} = {rhs} := by\n  simp only [{name},digest_stage_{i:02},digest_assoc]\n\n'
 text+=f'theorem {name}_success {params}'+(' (output : Digest8Q)'if i else '')+f' :\n    Success ({name} {args}) := by\n  rw [{name}_equation]\n'
 if i<24:text+=f'  apply bind\n  · exact digest_stage_{i:02}_success '+args+f'\n  intro next\n  exact digest_suffix_{i+1:02}_success public1 openings selectors next\n'
 else:text+=f'  exact digest_stage_{i:02}_success '+args+'\n'
 text+=f'\n#print axioms {name}_equation\n#print axioms {name}_success\nend PV_B3P_Success227\n';files[mod]=text
text='import PV_B3P_DigestSuffix00227\n'+header
text+=f'theorem digest_factor8 {params} :\n    reference_terminal.public_digest_lanes public1 openings selectors =\n      digest_suffix_00 public1 openings selectors := by\n  rfl\n#print axioms digest_factor8\n'
text+=f'theorem public_digest_success8 {params} :\n    Success (reference_terminal.public_digest_lanes public1 openings selectors) := by\n  rw [digest_factor8]\n  exact digest_suffix_00_success public1 openings selectors\n#print axioms public_digest_success8\nend PV_B3P_Success227\n'
files['PV_B3P_DigestBridge8227']=text
for m,text in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==text,m
 else:p.write_text(text)
print(json.dumps(dict(modules=list(files),strategy='one shallow suffix equation per stage; later suffixes locally irreducible; full bridge syntax factorization only')))
