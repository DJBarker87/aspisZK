import NKD_New
import NKD_Block
import NGT_BlockAssociation
set_option autoImplicit false
namespace AspisR1.NKD_Runtime
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Bytes32 := Array U8 32#usize
/-- Only the deployed SolanaDigest interpretation is exported. SHA value is runtime trust. -/
abbrev backend := NGT_BlockAssociation.runtime
/-- TX1:167 deployed instantiation: no generic function-pointer backend at the root. -/
theorem new_root (hashv : Slice (Slice U8) → Bytes32) (semantic : Bytes32)
 (variant : transport.Variant) :
 transcript.Transcript.new (backend hashv) () semantic variant =
 NKD_New.G (backend hashv) () semantic variant := NKD_New.root _ _ _ _
/-- TX1:165 deployed instantiation; exact digest input list and whole Result. -/
theorem absorb_root (hashv : Slice (Slice U8) → Bytes32) (state : Bytes32)
 (row : U8) (payload : Slice U8) :
 transcript.Transcript.absorb (backend hashv) ⟨state,()⟩ row payload =
 NKD_Absorb.G (backend hashv) ⟨state,()⟩ row payload := NKD_Absorb.root _ _ _ _
/-- TX1:166 deployed instantiation; native cuts' arbitrary replies are instantiated forward. -/
theorem block_root (hashv : Slice (Slice U8) → Bytes32) (state : Bytes32)
 (row : U8) (payload : Slice U8) :
 transcript.Transcript.block (backend hashv) ⟨state,()⟩ row payload =
 NKD_Block.G (backend hashv) ⟨state,()⟩ row payload := NKD_Block.root _ _ _ _
#print axioms new_root
#print axioms absorb_root
#print axioms block_root
#check @new_root
#check @absorb_root
#check @block_root
end AspisR1.NKD_Runtime
