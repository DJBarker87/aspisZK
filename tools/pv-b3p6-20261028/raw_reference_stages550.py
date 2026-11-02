"""Factor the pinned raw syntax one continuation at a time, with no limits raised."""
from pathlib import Path
import re,json,sys
L=Path('evidence/pv-b3p6-20261028/lean');R=L.parent/'resume18'
def emit(p,s):
 if '--check'in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
old=(L/'PV_B3P_P227_03d.lean').read_text();body=old.split('  := do\n',1)[1].split('\n\n\nend PV_B3P_227')[0]
starts=[body.index('  let a4 ←'),body.index('  let i20 ←'),body.index('  let i40 ←'),body.index('  let i60 ←'),body.index('  let a24 ←')]
prefix=body[:starts[0]];chunks=[body[starts[i]:starts[i+1]]for i in range(4)]+[body[starts[4]:]]
vals=[f'i{4+20*r+5*c}'for r in range(4)for c in range(4)];inputs=['a4','a6','a7','a8']
head='''namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227
set_option autoImplicit false
attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from
'''
# Remove the rejected monolithic delta equality from the definitions module.
p=L/'PV_B3P_RawTails550227.lean';s=p.read_text();cut=s.find('/-- Pure delta refactoring')
if cut>=0:s=s[:cut]+'''#print axioms raw_reference_tail0_550
#print axioms raw_native_tail0_550
end PV_B3P_Association550227
'''
emit(p,s)
for j in range(4,0,-1):
 predecessor='PV_B3P_RawTails550227'if j==4 else f'PV_B3P_RawRefTail{j+1}550227'
 arrays=['a','a1','a2','a3']if j==0 else inputs if j<4 else[]
 params=(' ('+' '.join(arrays)+' : Limbs32_550)')if arrays else''
 if j:params+=' ('+' '.join(vals[:4*j])+' : U64)'
 raw=''.join(chunks[j:])
 if j==0:
  typed=[]
  for line in raw.splitlines():
   m=re.match(r'  let (\w+|_) ← (.*)',line)
   if m:
    name,rhs=m.groups()
    if name in ['a4','a6','a7','a8']:typ='Limbs32_550'
    elif name in ['a24','a25','a26','a27']:typ='Limbs64_550'
    elif rhs.startswith('Array.index_usize a') and re.match(r'Array.index_usize (a4|a6|a7|a8) ',rhs):typ='U32'
    else:typ='U64'
    line=line.replace('let '+name+' ←','let '+name+' : '+typ+' ←',1)
   typed.append(line)
  raw='\n'.join(typed)+'\n'
 code=f'import {predecessor}\nimport PV_B3P_DigestCpsEq9227\n'+head
 code+=f'\ntheorem raw_reference_tail{j}_factor550'+params+' :\n    '+('(show Result Limbs64_550 from do\n'if j==0 else'(do\n')+raw+'\n    ) = raw_reference_tail'+str(j)+'_550 '+' '.join(arrays+vals[:4*j])+f' := by\n  unfold raw_reference_tail{j}_550\n'
 if j==4:code+='  rfl\n'
 else:
  for line in chunks[j].splitlines():
   m=re.match(r'  let (\w+) ←',line)
   if m:code+='  apply bind_equal9\n  intro '+m[1]+'\n'
  code+=f'  exact raw_reference_tail{j+1}_factor550 '+' '.join((inputs if j+1<4 else[])+vals[:4*(j+1)])+'\n'
 code+=f'\n#print axioms raw_reference_tail{j}_factor550\nend PV_B3P_Association550227\n'
 emit(L/f'PV_B3P_RawRefTail{j}550227.lean',code)
code='import PV_B3P_RawRefTail1550227\n'+head+'''
theorem raw_reference_factor550 (input : Array aspis_core.field.QM31 4#usize) :
    reference_poseidon.external_local_packed_raw input = (do
'''+prefix+'''  raw_reference_tail0_550 a a1 a2 a3) := by
  unfold reference_poseidon.external_local_packed_raw
'''
for line in prefix.splitlines():
 m=re.match(r'  let (\w+) ←',line)
 if m:code+='  apply bind_equal9\n  intro '+m[1]+'\n'
code+='  unfold raw_reference_tail0_550\n'
for line in chunks[0].splitlines():
 m=re.match(r'  let (\w+) ←',line)
 if m:code+='  apply bind_equal9\n  intro '+m[1]+'\n'
code+='''  exact raw_reference_tail1_factor550 a4 a6 a7 a8 i4 i9 i14 i19

#print axioms raw_reference_factor550
end PV_B3P_Association550227
'''
emit(L/'PV_B3P_RawReferenceFactor550227.lean',code)
p=L/'PV_B3P_RawSource550227.lean';s=p.read_text()
if 'import PV_B3P_RawReferenceFactor550227'not in s:s=s.replace('import PV_B3P_RawTail0550227','import PV_B3P_RawTail0550227\nimport PV_B3P_RawReferenceFactor550227')
emit(p,s)
print('four reference continuation factors and direct original root continuation factor generated; literal RefTail0 retired')
