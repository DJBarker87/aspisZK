import re
L=open('PRVEq_Op3I_Source_g1.lean').read().split('\n')
# 1-based line numbers from inspection: fresh Slice.Insts def = lines 16..26 (comment through closing brace), parse_shape fresh def 259..297, theorems 302..306 (Slice.Insts), 445..451 parse_shape
txt='\n'.join(L)
# drop the fresh Slice.Insts definition
a=txt.index('/-- Trait implementation: [core::array::equality')
b=txt.index('/-- [aspis_r1_cost_probe::compact::FINAL_LEN]')
txt=txt[:a]+txt[b:]
# replace fresh parse_shape def by parametric version
a=txt.index('/-- [aspis_r1_cost_probe::verifier::candidate::parse_shape]:')
b=txt.index('end PRVFresh_Op3I_Source')
fresh=txt[a:b]
fresh=fresh.replace('def verifier.candidate.parse_shape\n  (proof','def verifier.candidate.parse_shape_x\n  (eqF neF : {T U : Type} → {n : Usize} → core.cmp.PartialEq T U → Slice T → Std.Array U n → Result Bool)\n  (anyF : {T F : Type} → core.ops.function.FnMut F T Bool → core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T))\n  (proof')
fresh=fresh.replace('(Slice.Insts.CoreCmpPartialEqArray\n        8#usize core.cmp.PartialEqU8)','(Slice.Insts.CoreCmpPartialEqArrayX eqF neF\n        8#usize core.cmp.PartialEqU8)')
fresh=fresh.replace('core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any\n','anyF\n')
assert 'CoreCmpPartialEqArrayX' in fresh and 'anyF\n' in fresh
pre='''/-- PCWF: the frozen text calls the library items Slice.Insts.CoreCmpPartialEqArray.{eq,ne} (core::array::equality, HM-D) and
    core.slice.iter.Iter...any (core::iter::Iterator::any on slice::Iter, HM-B), which the Aeneas library of the closure does not define
    (they are external declarations in the fresh emission). They are abstracted here as parameters; the text is otherwise the fresh
    emission verbatim. -/
def Slice.Insts.CoreCmpPartialEqArrayX
  (eqF neF : {T U : Type} → {n : Usize} → core.cmp.PartialEq T U → Slice T → Std.Array U n → Result Bool)
  {T : Type} {U : Type} (N : Std.Usize)
  (cmpPartialEqInst : core.cmp.PartialEq T U) : core.cmp.PartialEq (Slice T) (Std.Array U N) := {
  eq := eqF cmpPartialEqInst
  ne := neF cmpPartialEqInst
}

'''
txt=txt[:a]+pre+fresh+txt[b:]
# drop generated theorems for Slice.Insts and parse_shape
def drop(name,txt):
    m=re.search(r'set_option maxHeartbeats 200000 in\ntheorem '+re.escape(name)+r' :.*?\n#print axioms '+re.escape(name)+r'\n',txt,re.S)
    assert m,name
    return txt[:m.start()]+txt[m.end():]
txt=drop('PRVEq.Op3I_Source.Slice.Insts.CoreCmpPartialEqArray',txt)
txt=drop('PRVEq.Op3I_Source.verifier.candidate.parse_shape',txt)
txt+='''
set_option maxHeartbeats 200000 in
/-- PCWF item B (Op3I_Source parse_shape): for every ParseShapeOps, the gate parse_shape ops equals the fresh 4bb3b3f emission with the
    library externals bound to the ops fields (eq := ops.sliceEq, ne := ops.sliceNe, any := ops.iterAny). Result class: the statement
    is DEPENDS_ON_LIBRARY_TRUST (HM-D core::array::equality PartialEq<[U;N]> for [T] eq/ne; HM-B core::iter::Iterator::any for
    core::slice::Iter), because the externals are not defined in the Aeneas library of the closure. -/
theorem PRVEq.Op3I_Source.verifier.candidate.parse_shape.bound (ops : Op3I_Source.ParseShapeOps) :
    Op3I_Source.verifier.candidate.parse_shape ops =
      Op3I_Source.PRVFresh_Op3I_Source.verifier.candidate.parse_shape_x
        (fun {T U n} inst => ops.sliceEq inst) (fun {T U n} inst => ops.sliceNe inst) (fun {T F} inst it f => ops.iterAny inst it f) := by
  funext proof
  delta Op3I_Source.verifier.candidate.parse_shape Op3I_Source.PRVFresh_Op3I_Source.verifier.candidate.parse_shape_x
  simp only [PRVEq.Op3I_Source.compact.PROOF_BYTES, PRVEq.Op3I_Source.compact.MAGIC, PRVEq.Op3I_Source.transport.Variant.tag,
    PRVEq.Op3I_Source.verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool]
  rfl
#print axioms PRVEq.Op3I_Source.verifier.candidate.parse_shape.bound
'''
open('PRVEq_Op3I_Source_g2.lean','w').write(txt)
