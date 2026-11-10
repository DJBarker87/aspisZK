import re
F='../prov-p1j-20261110/PCVJ_E002_emitted/raw/PCVJ_top/Types.lean'
ft=open(F).read()
def blk(name):
    m=re.search(r'(/--[^\n]*\n(?:    [^\n]*\n)*?)(structure '+re.escape(name)+r' where\n(?:  [^\n]*\n)+)',ft)
    return m.group(1)+m.group(2)
fresh=''.join(blk(n)+'\n' for n in ['verifier.BatchedWeights','verifier.Prepared','verifier.Accumulator'])
t=open('PRVEq_NEV_AccumulateRaw_Types_w1.lean').read()
# rename verifier.X -> X inside fresh namespace (gate names) for the three
fresh=fresh.replace('structure verifier.','structure ')
t=t.replace('end PRVFresh_NEV_AccumulateRaw_Types_w1\n',fresh+'end PRVFresh_NEV_AccumulateRaw_Types_w1\n',1)
P='NEV_AccumulateRaw.PRVFresh_NEV_AccumulateRaw_Types_w1'; G='NEV_AccumulateRaw'; E='PRVEq.NEV_AccumulateRaw.Types_w1'
add=f'''
/-- generic: an equivalence of element types lifts to Aeneas vectors and arrays (PCWM_) -/
def PRVEq.NEV_AccumulateRaw.Types_w1.vecEquiv {{α β : Type}} (e : α ≃ β) : alloc.vec.Vec α ≃ alloc.vec.Vec β where
  toFun x := ⟨x.val.map e, by have h := x.property; simpa using h⟩
  invFun y := ⟨y.val.map e.symm, by have h := y.property; simpa using h⟩
  left_inv x := by apply Subtype.ext; simp [List.map_map]
  right_inv y := by apply Subtype.ext; simp [List.map_map]
#print axioms PRVEq.NEV_AccumulateRaw.Types_w1.vecEquiv

def PRVEq.NEV_AccumulateRaw.Types_w1.arrEquiv {{α β : Type}} {{n : Std.Usize}} (e : α ≃ β) : Array α n ≃ Array β n where
  toFun x := ⟨x.val.map e, by have h := x.property; simpa using h⟩
  invFun y := ⟨y.val.map e.symm, by have h := y.property; simpa using h⟩
  left_inv x := by apply Subtype.ext; simp [List.map_map]
  right_inv y := by apply Subtype.ext; simp [List.map_map]
#print axioms PRVEq.NEV_AccumulateRaw.Types_w1.arrEquiv

def {E}.BatchedWeights.equiv : {P}.BatchedWeights ≃ {G}.BatchedWeights where
  toFun x := {{ «raw» := x.«raw», terms := x.terms }}
  invFun y := {{ «raw» := y.«raw», terms := y.terms }}
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl
#print axioms {E}.BatchedWeights.equiv

def {E}.Accumulator.equiv : {P}.Accumulator ≃ {G}.Accumulator where
  toFun x := {{ weights := (PRVEq.NEV_AccumulateRaw.Types_w1.vecEquiv {E}.aspis_core.field.QM31.equiv) x.weights, rhs := {E}.aspis_core.field.wide_exact.WideExact.equiv x.rhs, power := {E}.aspis_core.field.QM31.equiv x.power, next := x.next }}
  invFun y := {{ weights := (PRVEq.NEV_AccumulateRaw.Types_w1.vecEquiv {E}.aspis_core.field.QM31.equiv).symm y.weights, rhs := {E}.aspis_core.field.wide_exact.WideExact.equiv.symm y.rhs, power := {E}.aspis_core.field.QM31.equiv.symm y.power, next := y.next }}
  left_inv x := by
    cases x; simp
  right_inv y := by
    cases y; simp
#print axioms {E}.Accumulator.equiv

def {E}.Prepared.equiv : {P}.Prepared ≃ {G}.Prepared where
  toFun x := {{ variant := {E}.transport.Variant.equiv x.variant, roots := x.roots,
    gamma := {E}.aspis_core.field.wide_exact.WideExact.equiv x.gamma, kappa := {E}.aspis_core.field.wide_exact.WideExact.equiv x.kappa,
    alpha := (PRVEq.NEV_AccumulateRaw.Types_w1.arrEquiv {E}.aspis_core.field.wide_exact.WideExact.equiv) x.alpha,
    rho := {E}.aspis_core.field.QM31.equiv x.rho, queries := x.queries,
    semantic_alpha := (PRVEq.NEV_AccumulateRaw.Types_w1.arrEquiv {E}.aspis_core.field.QM31.equiv) x.semantic_alpha,
    z := (PRVEq.NEV_AccumulateRaw.Types_w1.arrEquiv {E}.aspis_core.circle.SecureCirclePoint.equiv) x.z,
    claim := {E}.aspis_core.field.wide_exact.WideExact.equiv x.claim, state := x.state }}
  invFun y := {{ variant := {E}.transport.Variant.equiv.symm y.variant, roots := y.roots,
    gamma := {E}.aspis_core.field.wide_exact.WideExact.equiv.symm y.gamma, kappa := {E}.aspis_core.field.wide_exact.WideExact.equiv.symm y.kappa,
    alpha := (PRVEq.NEV_AccumulateRaw.Types_w1.arrEquiv {E}.aspis_core.field.wide_exact.WideExact.equiv).symm y.alpha,
    rho := {E}.aspis_core.field.QM31.equiv.symm y.rho, queries := y.queries,
    semantic_alpha := (PRVEq.NEV_AccumulateRaw.Types_w1.arrEquiv {E}.aspis_core.field.QM31.equiv).symm y.semantic_alpha,
    z := (PRVEq.NEV_AccumulateRaw.Types_w1.arrEquiv {E}.aspis_core.circle.SecureCirclePoint.equiv).symm y.z,
    claim := {E}.aspis_core.field.wide_exact.WideExact.equiv.symm y.claim, state := y.state }}
  left_inv x := by
    cases x; simp
  right_inv y := by
    cases y; simp
#print axioms {E}.Prepared.equiv
'''
add=add.replace(',\n    ',', ')
open('PRVEq_NEV_AccumulateRaw_Types_w1.lean','w').write(t.rstrip()+'\n'+add)
