"""Name exact original suffixes, checking each head factor separately."""
from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';raw=(L/'PV_B3P_P227_11.lean').read_text().split('  := do\n',1)[1].split('\n\n\nend ',1)[0];ls=raw.splitlines();starts=[0]+[i for i,l in enumerate(ls)if i and re.match(r'  let (?:i2|digests3|i4|block(?:[1-9][0-9]*)?|i46) (?:←|:=)',l)];chunks=['\n'.join(ls[a:b])for a,b in zip(starts,starts[1:]+[len(ls)])]
params='''(public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
header='''namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry
'''
files={}
# One module names the exact suffix expressions, with no normalization or success claim.
s='import PV_B3P_DigestFields227\n'+header
for i in reversed(range(1,25)):
 ch='\n'.join(chunks[i:]);ch=re.sub(r'\bdigests'+str(i)+r'\b','output',ch);ch=re.sub(r'\bok\b','Result.ok',ch)
 s+=f'\ndef digest_raw_{i:02} {params} (output : Digest8Q) : Result Digest8Q := do\n'+ch+'\n'
s+='end PV_B3P_Success227\n';files['PV_B3P_DigestRaw8227']=s
for i in reversed(range(25)):
 mod=f'PV_B3P_DigestHead{i:02}227';s='import PV_B3P_DigestRaw8227\n'+f'import PV_B3P_DigestStage{i:02}227\nimport PV_B3P_DigestBranch227\n'+(f'import PV_B3P_DigestHead{i+1:02}227\n'if i<24 else '')+header
 args='public1 openings selectors'+(' output'if i else '')
 left=f'digest_raw_{i:02} {args}'if i else 'reference_terminal.public_digest_lanes '+args
 ch=chunks[i]
 if i:ch=re.sub(r'\bdigests'+str(i)+r'\b','output',ch)
 if i<24:ch+=f'\n  digest_raw_{i+1:02} public1 openings selectors digests{i+1}'
 ch=re.sub(r'\bok\b','Result.ok',ch)
 s+=f'\ndef digest_head_{i:02} {params}'+(' (output : Digest8Q)'if i else '')+' : Result Digest8Q := do\n'+ch+'\n'
 s+=f'\ntheorem digest_head_{i:02}_factor {params}'+(' (output : Digest8Q)'if i else '')+f' :\n    {left} = digest_head_{i:02} {args} := by\n  rfl\n'
 if i<24:s+=f'\nattribute [local irreducible] digest_raw_{i+1:02}\n'
 rhs=f'digest_stage_{i:02} '+args+(f' >>= digest_raw_{i+1:02} public1 openings selectors'if i<24 else '')
 s+=f'\ntheorem digest_head_{i:02}_equation {params}'+(' (output : Digest8Q)'if i else '')+f' :\n    digest_head_{i:02} {args} = {rhs} := by\n'
 if i==2:s+='  cases hr : public1.recipient <;>\n    simp only [digest_head_02,digest_stage_02,hr,digest_assoc,bind_tc_ok]\n'
 else:s+=f'  simp only [digest_head_{i:02},digest_stage_{i:02},digest_assoc,digest_if_bind,digest_option_bind]\n'
 s+=f'\ntheorem digest_raw_{i:02}_success {params}'+(' (output : Digest8Q)'if i else '')+f' :\n    Success ({left}) := by\n  rw [digest_head_{i:02}_factor,digest_head_{i:02}_equation]\n'
 if i<24:s+=f'  apply bind\n  · exact digest_stage_{i:02}_success {args}\n  intro next\n  exact digest_raw_{i+1:02}_success public1 openings selectors next\n'
 else:s+=f'  exact digest_stage_{i:02}_success {args}\n'
 s+=f'\n#print axioms digest_head_{i:02}_factor\n#print axioms digest_head_{i:02}_equation\n#print axioms digest_raw_{i:02}_success\nend PV_B3P_Success227\n';files[mod]=s
s=files['PV_B3P_DigestHead00227'].replace('import PV_B3P_DigestHead01227\n','')
s=s.split('\nattribute [local irreducible] digest_raw_01',1)[0]
s+='\n#print axioms digest_head_00_factor\nend PV_B3P_Success227\n'
s=s.replace(':= by\n  rfl\n',':= by\n  unfold reference_terminal.public_digest_lanes digest_head_00 digest_raw_01\n  congr 1 <;> (try funext next) <;> trace_state <;> rfl\n')
files['PV_B3P_DigestEntryFactor8227']=s
header=files['PV_B3P_DigestHead23227'].split('def digest_head_23',1)[0]
header=header[header.index('namespace '):]
imports='import PV_B3P_DigestHead24227\nimport PV_B3P_DigestEntryFactor8227\n'+''.join(f'import PV_B3P_DigestStage{i:02}227\n'for i in range(24))
out=imports+header
for i in reversed(range(1,24)):
 s=files[f'PV_B3P_DigestHead{i:02}227'];s=s[s.index('def digest_head_'):]
 s=s.rsplit('end PV_B3P_Success227',1)[0];out+=s+'\n'
s=files['PV_B3P_DigestHead00227'];s=s[s.index('attribute [local irreducible] digest_raw_01'):]
s=s.rsplit('end PV_B3P_Success227',1)[0];s=s.replace('#print axioms digest_head_00_factor\n','');out+=s+'\n'
out+='theorem public_digest_success8 (p : reference_terminal.SemanticPublic)\n    (o : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)\n    (s : reference_copy_terminal.Selectors) :\n    Success (reference_terminal.public_digest_lanes p o s) :=\n  digest_raw_00_success p o s\n#print axioms public_digest_success8\nend PV_B3P_Success227\n'
files['PV_B3P_DigestHeads8227']=out
files={m:s for m,s in files.items()if not m.startswith('PV_B3P_DigestHead')or m in ['PV_B3P_DigestHead24227','PV_B3P_DigestHeads8227']}
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
print(json.dumps(dict(modules=list(files),shape='exact raw suffixes; per-stage head equation; no whole-factor normalization')))
