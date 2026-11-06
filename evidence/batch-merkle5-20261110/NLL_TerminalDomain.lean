import NLL_Invocation
set_option autoImplicit false
noncomputable section
namespace NLL_TerminalDomain
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Derive the physical node carrier from the actual proof/slot producer.
Every prefix of this fixed slot is below the verifier byte gate, even before
using the stronger twelve-index producer invariant. -/
theorem source (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (batch : Nat) (kind slot : Usize) (hb : batch<2) (hk : kind.val<3) (value : slot.val=3*batch+kind.val)
 (count : Nat) :
 (NKV_ConcreteChildren.ops H).op3 proof slot=ok (nodeView H proof slot) ∧
 (nodeView H proof slot).val.length=32*OraclePortSelectedDraft.capacity (3*batch+kind.val) ∧
 (MultiproofConeSlotTail.prefixNodes (nodeView H proof slot) count).val.length≤9216 := by
 obtain ⟨nodes,read,width,bytes⟩:=NKV_SlotInvocation.physical H proof len p wire batch kind.val hb hk slot value
 have selected : nodeView H proof slot=nodes := by unfold nodeView;rw [read]
 rw [selected]
 obtain ⟨cap,capRead,capValue,small⟩:=NKV_SlotInvocation.capacity slot (by omega)
 have bound : OraclePortSelectedDraft.capacity (3*batch+kind.val)≤172 := by rw [←value,←capValue];exact small
 refine ⟨read,width,?_⟩
 simp only [MultiproofConeSlotTail.prefixNodes,List.length_take]
 omega

set_option pp.proofs false
#print source
#print axioms source
end NLL_TerminalDomain
end
