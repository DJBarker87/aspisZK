from pathlib import Path
import importlib.util
T=Path(__file__).parent;R=T.resolve().parents[1];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
sp=importlib.util.spec_from_file_location('w',T/'write-module.py');w=importlib.util.module_from_spec(sp);sp.loader.exec_module(w)
s=(L/'PV_RunJoin_CircleNeutralR24Body53.lean').read_text();a=s.index('  let i8 ← a1 * e1');b=s.index('\ntheorem canonical',a);tail=s[a:b].strip('\n').replace(' i1',' PV_RunJoin_CircleNeutralR24Leaf53.square')
# Only replace the exact old PP variable; preserve i10, i11, ... identifiers.
import re
tail=s[a:b].strip('\n');tail=re.sub(r'\bi1\b','PV_RunJoin_CircleNeutralR24Leaf53.square',tail)
head='''abbrev Q := (U32 × U32) × (U32 × U32)
'''
body=head+'def tail (left right : Q) (u v : U64) : Result (Option Q) := do\n'
for n,f in [('a1','left.1.1'),('b1','left.1.2'),('c1','left.2.1'),('d1','left.2.2'),('e1','right.1.1'),('f1','right.1.2'),('g1','right.2.1'),('h1','right.2.2')]:body+=f'  let {n} := UScalar.cast .U64 {f}\n'
body+=tail+'\n'
w.write('PV_RunJoin_CircleNeutralR24Tail53',['R1Z.PV_RunJoin_CircleNeutralR24Leaf53'],body,['tail'])
body=head+'''attribute [local irreducible] PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64
attribute [local irreducible] PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call

theorem body (left right : Q) : PV_RunJoin_CircleNeutralR24Body53.body left right = (do
    let u ← PV_RunJoin_CircleNeutralR24U53.source left.2.1 left.2.2 right.2.1 right.2.2
    let v ← PV_RunJoin_CircleNeutralR24V53.source left.2.1 left.2.2 right.2.1 right.2.2
    PV_RunJoin_CircleNeutralR24Tail53.tail left right u v) := by
  unfold PV_RunJoin_CircleNeutralR24Body53.body PV_RunJoin_CircleNeutralR24U53.source
    PV_RunJoin_CircleNeutralR24V53.source PV_RunJoin_CircleNeutralR24Tail53.tail
  simp only [lift,bind_tc_ok,PV_RunJoin_CircleNeutralR24Leaf53.pp,bind_assoc_eq]
  rfl
'''
w.write('PV_RunJoin_CircleNeutralR24Split53',['R1Z.PV_RunJoin_CircleNeutralR24Body53','R1Z.PV_RunJoin_CircleNeutralR24Tail53','R1Z.PV_RunJoin_CircleNeutralR24U53','R1Z.PV_RunJoin_CircleNeutralR24V53'],body,['body'])
body=head+'''open PV_RunJoin_CircleNeutralShape53

theorem complete (left right : Q) (hl : QC left) (hr : QC right) :
    PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul left right =
      PV_RunJoin_CircleNeutralR24Tail53.tail left right
        (PV_RunJoin_CircleNeutralR24Word53.word (AspisV8R19.PartialProduct.foldOnce
          (left.2.1.val*right.2.1.val+4611686014132420609-left.2.2.val*right.2.2.val)))
        (PV_RunJoin_CircleNeutralR24Word53.word (AspisV8R19.PartialProduct.foldOnce
          (left.2.1.val*right.2.2.val+left.2.2.val*right.2.1.val))) := by
  rw [PV_RunJoin_CircleNeutralR24Body53.canonical left right hl hr,
    PV_RunJoin_CircleNeutralR24Split53.body]
  rw [PV_RunJoin_CircleNeutralR24U53.complete _ _ _ _ hl.2.1 hl.2.2 hr.2.1 hr.2.2,bind_tc_ok,
    PV_RunJoin_CircleNeutralR24V53.complete _ _ _ _ hl.2.1 hl.2.2 hr.2.1 hr.2.2,bind_tc_ok]
'''
w.write('PV_RunJoin_CircleNeutralR24Prefix53',['R1Z.PV_RunJoin_CircleNeutralR24Split53'],body,['complete'])
