import MultiproofConePhysicalTransport

set_option autoImplicit false
namespace AspisR1.MultiproofConePhysicalAddress
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalDigest MultiproofConePhysicalTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open OracleDecisionMultiTree

theorem node_bytes (left right : State) :
    BinMerkle32Path.nodeBytes (children left right)=bytes left ++ bytes right := by
  change List.ofFn (fun i : Fin (32+32) => BinMerkle32Path.childByte (children left right) i)=_
  rw [List.ofFn_add]
  apply congrArg₂ List.append
  · apply congrArg List.ofFn
    funext i
    simp [BinMerkle32Path.childByte,children,Nat.div_eq_of_lt i.isLt,Nat.mod_eq_of_lt i.isLt]
  · apply congrArg List.ofFn
    funext i
    have div : (32+i.val)/32=1 := by omega
    have mod : (32+i.val)%32=i.val := by omega
    simp [BinMerkle32Path.childByte,children,div,mod,Nat.mod_eq_of_lt i.isLt]

/-- The physical hashv components flatten to the EXACT frozen parent address,
with the occupied or supplied child order already fixed by the node step. -/
theorem parent_address (left right : Digest) :
    flatten (parts left right)=BinMerkle32Path.nodeInput (children (decodeState left) (decodeState right)) := by
  rw [BinMerkle32Path.nodeInput,node_bytes,digest_bytes,digest_bytes]
  simp [flatten,parts,MultiproofConeCanonical.bytesOf]
  rfl

#print axioms node_bytes
#print axioms parent_address
end AspisR1.MultiproofConePhysicalAddress
