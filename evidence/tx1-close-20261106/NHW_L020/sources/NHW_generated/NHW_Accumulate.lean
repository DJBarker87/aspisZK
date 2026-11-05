import NHW_QueryDictionary
import NHL_BindOn
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_Accumulate
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NHW_QueryDictionary
/-- The shared source prefix and all three canonical arithmetic transports
identify the entire accumulation Result. No successful prefix is assumed. -/
theorem source (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (node : U32) (value : aspis_core.field.wide_exact.WideExact) (b : verifier.BatchedWeights)
 (hv : NBO_TailDomain.WideCanonical value) (hr : NBO_TailDomain.WideCanonical a.rhs)
 (hp : NBF_PowerStep.Canonical a.power) (hq : NBF_PowerStep.Canonical p.rho) :
 verifier.accumulate_batched_with_node (model base) p a node value b=
 verifier.accumulate_batched_with_node (NFS_QueryOps.installed (model base)) p a node value b := by
 rw [shell,shell,←prefix_same]
 apply NHL_BindOn.reached
 intro mid _
 simp only [lift,bind_tc_ok]
 change (do
   let product ← SAQ_MixedSource.mulE value a.power
   let rhs ← SAQ_Arithmetic.add a.rhs product
   let power ← SAQ_Arithmetic.mulK a.power p.rho
   ok ({a with rhs:=rhs,power:=power,next:=Usize.wrapping_add a.next 1#usize},
     {mid with terms:=Usize.wrapping_add mid.terms 1#usize})) = _
 rw [NHW_FieldTransport.product value a.power hv hp]
 obtain ⟨product,run,canonical⟩ := NBO_FieldSemantics.product_total value a.power hv hp
 rw [run,bind_tc_ok]
 rw [NHW_FieldTransport.add a.rhs product hr canonical,NHW_FieldTransport.power a.power p.rho hp hq]
 rfl
#print axioms source
end AspisR1.NHW_Accumulate
