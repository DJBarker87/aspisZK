from pathlib import Path
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
vars=['left.1.1.val','left.1.2.val','left.2.1.val','left.2.2.val','right.1.1.val','right.1.2.val','right.2.1.val','right.2.2.val']
letters=dict(zip('abcdefgh',vars)); P='4611686014132420609';p='2147483647'
# Named primitive rewrites follow the original source order; no arithmetic body unfolds.
seqs=[ [('mul','a*e'),('add',None),('mul','b*f'),('sub',None),('mul','2*u'),('add',None),('mul','3*2147483647'),('add',None),('sub',None)], [('mul','a*f'),('mul','b*e'),('add',None),('add',None),('mul','2*v'),('add',None)], [('mul','a*g'),('mul','c*e'),('add',None),('mul','2*4611686014132420609'),('add',None),('mul','b*h'),('sub',None),('mul','d*f'),('sub',None)], [('mul','a*h'),('mul','b*g'),('add',None),('mul','c*f'),('add',None),('mul','d*e'),('add',None)] ]
ns=['a*e+4611686014132420609-b*f+2*u+3*2147483647-v','a*f+b*e+u+2*v','a*g+c*e+2*4611686014132420609-b*h-d*f','a*h+b*g+c*f+d*e']
def expand(s):
 import re
 return re.sub(r'\b[a-h]\b',lambda m:letters[m[0]],s)
for j in range(4):
 name=f'PV_RunJoin_R24Equation{j}_54'
 s=f'''import R1Z.PV_RunJoin_R24Cell{j}_54
import R1Z.PV_RunJoin_CircleNeutralR24Word53
import R1Z.PV_RunJoin_CircleNeutralR24Bounds53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.{name}
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralR24Word53
abbrev Q := (U32 × U32) × (U32 × U32)
def accumulator (left right : Q) (u v : Nat) : Nat := {expand(ns[j])}
theorem complete (left right : Q) (hl : QC left) (hr : QC right)
    (u v : Nat) (hu : u<6442450941) (hv : v<6442450941) :
    PV_RunJoin_R24Cell{j}_54.cell left right (word u) (word v)=
      PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 (word (accumulator left right u v)) := by
'''
 for k,(term,prf) in enumerate(zip(vars,['hl.1.1','hl.1.2','hl.2.1','hl.2.2','hr.1.1','hr.1.2','hr.2.1','hr.2.2'])):s+=f'  have h{k} : {term}<2147483647 := {prf}\n'
 for a in 'abcd':
  for b in 'efgh':s+=f'  have h{a}{b} : {expand(a+"*"+b)}<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h{"abcd".index(a)} h{4+"efgh".index(b)}\n'
 s+='''  have hsquare : PV_RunJoin_CircleNeutralR24Leaf53.square=word 4611686014132420609 := by
    apply UScalar.eq_of_val_eq
    rw [PV_RunJoin_CircleNeutralR24Leaf53.square_val,value _ (by decide)]
  have hprime : core.convert.num.FromU64U32.from PV_RunJoin_CircleR72Raw52.field.P=word 2147483647 := rfl
'''
 s+=f'  unfold PV_RunJoin_R24Cell{j}_54.cell accumulator\n  simp only [widen,hsquare,hprime,show (2#u64)=word 2 from rfl,show (3#u64)=word 3 from rfl,lift,bind_tc_ok]\n'
 for op,t in seqs[j]:
  if op=='mul':s+='  rw [mul _ _ (by omega) (by omega) (by omega),bind_tc_ok]\n'
  elif op=='add':s+='  rw [add]\n'
  else:s+='  rw [sub _ _ (by omega) (by omega)]\n'
 s+='  cases PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 _ <;> rfl\n#print axioms accumulator\n#print axioms complete\nend R1Z.'+name+'\n'
 (L/(name+'.lean')).write_text(s)
