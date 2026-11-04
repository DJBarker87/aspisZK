import Lean
import NFN_PhaseTransport
import NFS_NEV_AccumulateTail
import NFS_NEV_PrimitiveTotal

set_option autoImplicit false
noncomputable section
namespace NFS_NEV_TailModel
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody

def fields (base : Ops) : Ops :=
 {base with op2:=NBO_FieldSemantics.add,op3:=NBO_FieldSemantics.product,op9:=NBO_FieldSemantics.power}
def toPair (pair : NEV_AccumulateRaw.Accumulator × NEV_AccumulateRaw.BatchedWeights) :
    verifier.Accumulator × verifier.BatchedWeights := (toAccumulator pair.1,toWeights pair.2)
def tail (p : verifier.Prepared) (a : verifier.Accumulator) (value : NBF_RowInstall.E)
    (middle : verifier.BatchedWeights) : Result (verifier.Accumulator × verifier.BatchedWeights) := do
 let terms ← middle.terms+1#usize
 let product ← NBO_FieldSemantics.product value a.power
 let rhs ← NBO_FieldSemantics.add a.rhs product
 let power ← NBO_FieldSemantics.power a.power p.rho
 let next ← a.next+1#usize
 ok ({a with rhs:=rhs,power:=power,next:=next},{middle with terms:=terms})

/-- All three intermediate field results and their domains are derived, not
hypotheses. Both checked counter outcomes and full returned carriers remain. -/
theorem association (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (value : RawE) (middle : NEV_AccumulateRaw.BatchedWeights)
    (hv : NBO_TailDomain.WideCanonical (toE value))
    (hr : NBO_TailDomain.WideCanonical (toE a.rhs))
    (hp : NBF_PowerStep.Canonical (toQ a.power))
    (hq : NBF_PowerStep.Canonical (toQ p.rho)) :
    (do let out ← NFS_NEV_AccumulateTail.tail p a value middle;ok (toPair out)) =
      tail (toPrepared p) (toAccumulator a) (toE value) (toWeights middle) := by
  obtain ⟨product,productRun,productCanonical⟩ := NFS_NEV_PrimitiveBindings.product_returns value a.power hv hp
  obtain ⟨rhs,rhsRun,rhsCanonical⟩ := NFS_NEV_PrimitiveTotal.add a.rhs product hr productCanonical
  obtain ⟨power,powerRun,powerCanonical⟩ := NFS_NEV_PrimitiveTotal.power a.power p.rho hp hq
  have modelProduct : NBO_FieldSemantics.product (toE value) (toQ a.power)=ok (toE product) := by
    simpa only [productRun,bind_tc_ok] using (NFS_NEV_PrimitiveBindings.product value a.power hv hp).symm
  have modelRhs : NBO_FieldSemantics.add (toE a.rhs) (toE product)=ok (toE rhs) := by
    simpa only [rhsRun,bind_tc_ok] using (NFS_NEV_PrimitiveBindings.add a.rhs product hr productCanonical).symm
  have modelPower : NBO_FieldSemantics.power (toQ a.power) (toQ p.rho)=ok (toQ power) := by
    simpa only [powerRun,bind_tc_ok] using (NFS_NEV_PrimitiveBindings.power a.power p.rho hp hq).symm
  simp only [NFS_NEV_AccumulateTail.tail,tail,NEV_AccumulateRaw.trace.value,
    productRun,rhsRun,powerRun,modelProduct,modelRhs,modelPower,bind_assoc_eq,bind_tc_ok,
    toPair,toPrepared,toAccumulator,toWeights]
#print axioms association
end NFS_NEV_TailModel
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
