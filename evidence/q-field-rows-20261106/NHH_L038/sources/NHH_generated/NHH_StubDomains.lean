import NHH_CMTrace
import NHH_QTrace
set_option autoImplicit false
noncomputable section
namespace NHH_StubDomains
open Aeneas Aeneas.Std
open AspisV8R19 AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
def MCanon (x : U32) : Prop := x.val<2147483647

theorem scalar_canonical (x : M31Exact) : MCanon (encodeBase x) := by
 simpa only [MCanon,ComplexBaseExecution.encodeBase_val] using ZMod.val_lt x

def CMEventDomain : NHH_CMTrace.Event → Prop
 | .product a b out => MCanon a ∧ MCanon b ∧ MCanon out
 | .backend a out => MCanon a ∧ a≠0#u32 ∧ MCanon out

theorem cm_log (x : CM31Exact) (hx : x≠0) (event : NHH_CMTrace.Event)
 (he : event∈NHH_CMTrace.log x) : CMEventDomain event := by
 simp only [NHH_CMTrace.log,List.mem_cons,List.not_mem_nil,or_false] at he
 rcases he with rfl|rfl|rfl|rfl|rfl
 · exact ⟨scalar_canonical _,scalar_canonical _,scalar_canonical _⟩
 · exact ⟨scalar_canonical _,scalar_canonical _,scalar_canonical _⟩
 · exact ⟨(NHH_CMTrace.backend_domain x hx).1,(NHH_CMTrace.backend_domain x hx).2,scalar_canonical _⟩
 · exact ⟨scalar_canonical _,scalar_canonical _,scalar_canonical _⟩
 · exact ⟨scalar_canonical _,scalar_canonical _,scalar_canonical _⟩

def QEventDomain : NHH_QTrace.Event → Prop
 | .square a out => NHH_CMInverse.Canon a ∧ NHH_CMInverse.Canon out
 | .inverse a out => NHH_CMInverse.Canon a ∧ NHH_CMInverse.decode a≠0 ∧ NHH_CMInverse.Canon out
 | .product a b out => NHH_CMInverse.Canon a ∧ NHH_CMInverse.Canon b ∧ NHH_CMInverse.Canon out

theorem qm_log (x : QM31Exact) (hx : x≠0) (event : NHH_QTrace.Event)
 (he : event∈NHH_QTrace.log x) : QEventDomain event := by
 simp only [NHH_QTrace.log,List.mem_cons,List.not_mem_nil,or_false] at he
 rcases he with rfl|rfl|rfl|rfl|rfl
 · exact ⟨NHH_CMBridge.encoded_canonical _,NHH_CMBridge.encoded_canonical _⟩
 · exact ⟨NHH_CMBridge.encoded_canonical _,NHH_CMBridge.encoded_canonical _⟩
 · exact ⟨(NHH_QTrace.inverse_domain x hx).1,(NHH_QTrace.inverse_domain x hx).2,NHH_CMBridge.encoded_canonical _⟩
 · exact ⟨NHH_CMBridge.encoded_canonical _,NHH_CMBridge.encoded_canonical _,NHH_CMBridge.encoded_canonical _⟩
 · exact ⟨NHH_CMBridge.encoded_canonical _,NHH_CMBridge.encoded_canonical _,NHH_CMBridge.encoded_canonical _⟩

#print axioms scalar_canonical
#print axioms cm_log
#print axioms qm_log
end NHH_StubDomains
end
