import LPq_SixPoints
import XRy_ClaimSum
set_option autoImplicit false
namespace AspisR1.LPq_WeightedStep
open Aeneas Aeneas.Std Result LPi_FieldValues LPq_FieldPorts XRo_Join_Carriers

theorem add (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z ∧ canonE z ∧
      aspis_core.field.wide_exact.WideExact.add (wide x) (wide y)=ok (wide z) := by
  obtain ⟨lo,el,cl,tl⟩ := LPq_TowerPorts.add x.c0 y.c0 hx.1 hy.1
  obtain ⟨hi,eh,ch,th⟩ := LPq_TowerPorts.add x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨lo,hi⟩,?_,⟨cl,ch⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,el,eh,bind_tc_ok]
  · change (do
      let a ← XRn_Join_Field.field.QM31.add (qm x.c0) (qm y.c0)
      let b ← XRn_Join_Field.field.QM31.add (qm x.c1) (qm y.c1)
      ok (⟨XRn_Join_FieldExternal.oldQ a,XRn_Join_FieldExternal.oldQ b⟩ : C.E)) = _
    rw [tl,bind_tc_ok,th,bind_tc_ok]
    rfl

abbrev Seven := Array NE 7#usize
def canonical (a : Seven) : Prop := ∀ x ∈ a.val, canonE x

theorem canonical_port (a : Seven) (ha : canonical a) :
    XRy_ClaimSumStep.canonical (arr wide a) := by
  intro i hi
  simp only [XRy_ClaimSumStep.cell,arr,List.getElem_map]
  apply LPq_WidePorts.canonical
  exact ha _ (List.getElem_mem _)

def step (k parts : Seven) (sum : NE) (i : Usize) : Result NE := do
  let part ← Array.index_usize parts i
  let power ← Array.index_usize k i
  let term ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul power part
  FIo_Native.aspis_core.field.wide_exact.WideExact.add sum term

/-- ONE native arithmetic step after the operand-selection cut. The same
selected carriers feed multiplication and addition; no arithmetic is stubbed
or proved in Kani here. -/
theorem paired (k parts : Seven) (sum : NE) (i : Usize) (hi : i.val<7)
    (hk : canonical k) (hp : canonical parts) (hs : canonE sum) :
    ∃ out, step k parts sum i=ok out ∧ canonE out ∧
      XRy_ClaimSumStep.step (arr wide k) (arr wide parts) (wide sum) i=ok (wide out) := by
  have ik : i.val<k.val.length := by rw [k.property]; exact hi
  have ip : i.val<parts.val.length := by rw [parts.property]; exact hi
  obtain ⟨term,et,ct,rt⟩ := LPq_WidePorts.mul k.val[i.val] parts.val[i.val]
    (hk _ (List.getElem_mem ik)) (hp _ (List.getElem_mem ip))
  obtain ⟨out,eo,co,ro⟩ := add sum term hs ct
  refine ⟨out,?_,co,?_⟩
  · simp only [step,XRy_ArrayRead.read parts i hi,XRy_ArrayRead.read k i hi,bind_tc_ok,et,eo]
  · simp only [XRy_ClaimSumStep.step,XRy_ArrayRead.mapped wide parts i hi,
      XRy_ArrayRead.mapped wide k i hi,bind_tc_ok,rt,ro]

#print axioms add
#print axioms canonical_port
#print axioms paired
end AspisR1.LPq_WeightedStep
