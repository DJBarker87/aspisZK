import NFT_Reference.Funs
import NFT_QBytes
import NFT_WideNew
set_option autoImplicit false
namespace NFT_ReferenceEq
open Aeneas Aeneas.Std Result

theorem canonical (x : U32) : NFT_Reference.canonical_ref x=ok (NFT_WideNew.reduce x) := by
  rfl

theorem cm (a b : U32) : NFT_Reference.cm_bytes_ref a b=
    ok (Array.make 8#usize (NFT_Bytes.cmBytes ⟨a,b⟩) (hl := by simp [NFT_Bytes.cmBytes,NFT_Bytes.qmBytes,core.num.U32.to_le_bytes,BitVec.toLEBytes])) := by
  rfl

theorem qm (a b c d : U32) : NFT_Reference.qm_bytes_ref a b c d=
    ok (Array.make 16#usize (NFT_Bytes.qmBytes ⟨⟨a,b⟩,⟨c,d⟩⟩) (hl := by simp [NFT_Bytes.cmBytes,NFT_Bytes.qmBytes,core.num.U32.to_le_bytes,BitVec.toLEBytes])) := by
  rfl

#print axioms canonical
#print axioms cm
#print axioms qm
end NFT_ReferenceEq
