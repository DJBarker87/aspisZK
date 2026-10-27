import JGh_TX2_M0LeafSources10
import JGh_TX2_M0LeafSources12
import JGh_TX2_M0LeafSources14
import JGh_TX2_M0LeafSources16
import JGh_TX2_M0LeafSources18
import JGh_TX2_M0LeafSources20
import JGh_TX2_M1LeafSources10
import JGh_TX2_M1LeafSources12
import JGh_TX2_M1LeafSources14
import JGh_TX2_M1LeafSources16
import JGh_TX2_M1LeafSources18
import JGh_TX2_M1LeafSources20
import JGh_TX2_M1Root
import JGf_TX2_M0Root
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_LeafBinding
open Aeneas Aeneas.Std Result
attribute [local irreducible] JGc_TX2_HashBytes.bytes AspisV8R19.SqueezeOracleBridge.flatten Port4B_LeafCode.input
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
theorem bytes_injective (a b : Bytes) (same : a.map Fin.val=b.map Fin.val) : a=b := by
  exact List.map_injective Fin.val_injective same
#print axioms bytes_injective
def actualInput0 (base : Nat) : Bytes := match base with
  | 132355 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨10,by decide⟩))
  | 218094 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨11,by decide⟩))
  | 178080 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨12,by decide⟩))
  | 149624 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨13,by decide⟩))
  | 166165 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨14,by decide⟩))
  | 42158 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨15,by decide⟩))
  | 179622 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨16,by decide⟩))
  | 21248 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨17,by decide⟩))
  | 63860 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨18,by decide⟩))
  | 55377 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨19,by decide⟩))
  | 185637 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨20,by decide⟩))
  | 14297 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 0#usize (JFo_Opening.value ⟨21,by decide⟩))
  | _ => []
theorem inputs0 : JGf_TX2_M0Roots.InputLaw actualInput0 := by
  intro b hb
  simp only [JGf_TX2_M0Roots.indices,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf10.address.trans JGf_TX2_M0Roots.numeric000.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf11.address.trans JGf_TX2_M0Roots.numeric001.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf12.address.trans JGf_TX2_M0Roots.numeric002.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf13.address.trans JGf_TX2_M0Roots.numeric003.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf14.address.trans JGf_TX2_M0Roots.numeric004.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf15.address.trans JGf_TX2_M0Roots.numeric005.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf16.address.trans JGf_TX2_M0Roots.numeric006.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf17.address.trans JGf_TX2_M0Roots.numeric007.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf18.address.trans JGf_TX2_M0Roots.numeric008.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf19.address.trans JGf_TX2_M0Roots.numeric009.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf20.address.trans JGf_TX2_M0Roots.numeric010.symm)
  · exact bytes_injective _ _ (JGh_TX2_M0Leaf21.address.trans JGf_TX2_M0Roots.numeric011.symm)
#print axioms inputs0
theorem root0 : OracleDecisionMultiTree.root JFp_SHADigest.digest
    (OracleDecisionMultiBuild.build JGf_TX2_M0Roots.indices actualInput0 JGf_TX2_M0Roots.siblingAt 18 0)=JGf_TX2_M0Root.retainedRoot :=
  JGf_TX2_M0Root.source _ _ inputs0 (by intro h _ b _;rfl)
#print axioms root0
def actualInput1 (base : Nat) : Bytes := match base with
  | 132355 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨10,by decide⟩))
  | 218094 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨11,by decide⟩))
  | 178080 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨12,by decide⟩))
  | 149624 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨13,by decide⟩))
  | 166165 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨14,by decide⟩))
  | 42158 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨15,by decide⟩))
  | 179622 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨16,by decide⟩))
  | 21248 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨17,by decide⟩))
  | 63860 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨18,by decide⟩))
  | 55377 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨19,by decide⟩))
  | 185637 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨20,by decide⟩))
  | 14297 => AspisV8R19.SqueezeOracleBridge.flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨21,by decide⟩))
  | _ => []
theorem inputs1 : JGh_TX2_M1Roots.InputLaw actualInput1 := by
  intro b hb
  simp only [JGh_TX2_M1Roots.indices,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf10.address.trans JGh_TX2_M1Roots.numeric000.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf11.address.trans JGh_TX2_M1Roots.numeric001.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf12.address.trans JGh_TX2_M1Roots.numeric002.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf13.address.trans JGh_TX2_M1Roots.numeric003.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf14.address.trans JGh_TX2_M1Roots.numeric004.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf15.address.trans JGh_TX2_M1Roots.numeric005.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf16.address.trans JGh_TX2_M1Roots.numeric006.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf17.address.trans JGh_TX2_M1Roots.numeric007.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf18.address.trans JGh_TX2_M1Roots.numeric008.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf19.address.trans JGh_TX2_M1Roots.numeric009.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf20.address.trans JGh_TX2_M1Roots.numeric010.symm)
  · exact bytes_injective _ _ (JGh_TX2_M1Leaf21.address.trans JGh_TX2_M1Roots.numeric011.symm)
#print axioms inputs1
theorem root1 : OracleDecisionMultiTree.root JFp_SHADigest.digest
    (OracleDecisionMultiBuild.build JGh_TX2_M1Roots.indices actualInput1 JGh_TX2_M1Roots.siblingAt 18 0)=JGh_TX2_M1Root.retainedRoot :=
  JGh_TX2_M1Root.source _ _ inputs1 (by intro h _ b _;rfl)
#print axioms root1
end AspisR1.JGk_TX2_LeafBinding
end
