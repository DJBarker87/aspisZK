#!/usr/bin/env python3
"""PCVA_nhj.py: NOMINAL transport for NHJ_SnapshotReference.Funs (P4a obligation D3).
Gate: `abbrev NHJ_SnapshotReference.ProgramError := NGL_MetaReference.ProgramError`, so constructors are reached as
`NGL_MetaReference.ProgramError.<C>`. Fresh Types declares its own inductive `ProgramError` with the same constructor list
(token-equal after whitespace normalisation against the NGL_MetaReference Types text, checked below). The fresh Funs text is
used unchanged except that every constructor reference `ProgramError.<C>` is qualified as `NGL_MetaReference.ProgramError.<C>`.
A Lean-checked constructor-wise Equiv between a verbatim copy of the fresh inductive and the compiled gate inductive is added
as the transport theorem PRVEq.NHJ_SnapshotReference.ProgramError.equiv."""
import re,sys
fresh_types=open('../prov-p5-20261109/inputs/fresh_NHJ_SnapshotReference_Funs/Types.lean').read()
m=re.search(r'inductive ProgramError where\n(.*?)\n\n',fresh_types,re.S)
body=m.group(1)
ctors=re.findall(r'^\| (\w+) :(?: (?:Std\.U32|String) →)?() ?ProgramError$',body,re.M)
ctors=[(n,'→' in l) for n,l in zip([c[0] for c in ctors],body.split('\n'))]
names=[c[0] for c in ctors]
assert len(names)==26,len(names)
t=open('PRVEq_NHJ_SnapshotReference_Funs_P3.lean').read()
pat=re.compile(r'(?<![\w.])ProgramError\.('+'|'.join(names)+r')\b')
t2=pat.sub(r'NGL_MetaReference.ProgramError.\1',t)
# transport theorem: verbatim fresh inductive copy
ind='inductive PRVFreshTypes_NHJ_SnapshotReference.ProgramError where\n'+body.replace('ProgramError\n','ProgramError\n')
ind=re.sub(r'→ ProgramError','→ PRVFreshTypes_NHJ_SnapshotReference.ProgramError',ind)
ind=re.sub(r': ProgramError(\s|$)',r': PRVFreshTypes_NHJ_SnapshotReference.ProgramError\1',ind,flags=re.M)
F='PRVFreshTypes_NHJ_SnapshotReference.ProgramError';G='NGL_MetaReference.ProgramError'
def arm(a,b):
    out=[]
    for n,has in ctors:
        if has: out.append(f'  | {a}.{n} x => {b}.{n} x')
        else: out.append(f'  | {a}.{n} => {b}.{n}')
    return '\n'.join(out)
tr=f'''
-- ---- P3 NOMINAL transport (class NOMINAL; see PCVA_CLASSIFICATION.json): fresh inductive == gate inductive, constructor-wise
{ind}
def PRVEq_NHJ_toGate : {F} → {G}
{arm(F,G)}
def PRVEq_NHJ_ofGate : {G} → {F}
{arm(G,F)}
theorem PRVEq.NHJ_SnapshotReference.ProgramError.left_inv (x : {F}) : PRVEq_NHJ_ofGate (PRVEq_NHJ_toGate x) = x := by
  cases x <;> rfl
theorem PRVEq.NHJ_SnapshotReference.ProgramError.right_inv (x : {G}) : PRVEq_NHJ_toGate (PRVEq_NHJ_ofGate x) = x := by
  cases x <;> rfl
#print axioms PRVEq.NHJ_SnapshotReference.ProgramError.left_inv
#print axioms PRVEq.NHJ_SnapshotReference.ProgramError.right_inv
'''
# placing: before 'noncomputable section' we need the inductive outside; append at end (inductive allowed inside noncomputable section)
t2=t2.rstrip('\n')+'\n'+tr
open('PRVEq_NHJ_SnapshotReference_Funs_P3b.lean','w').write(t2)
print(len(names))
