import Port4B_LeafCode
import Port4B_PhysicalCalls

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_LeafInstall
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical

/-- Concrete reached opening and one-call leaf children. Other native
children remain visible in base; this is not a whole-batch certificate. -/
def install (base : Port3_NativeBatchBody.Ops) : Port3_NativeBatchBody.Ops :=
  {base with op2:=Port4B_Opening.opening,op6:=Port4B_LeafCode.native}

/-- The physical selected opening and the installed native hash return are
bound to the SAME P6 address, with one ordered read on any prefix log. -/
theorem selected_call (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (law : ∀ input, D.digest hash input=ok (MultiproofConePhysicalTransport.rawOracle H input))
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (q : Fin 22 → Fin 262144) (batch pos : Nat) (kind i : Usize)
    (mem : pos∈OraclePortFrozenOrder.sortedPositions q batch kind.val)
    (rebased : i.val=(if batch=0 then 0 else 10)+
      (MultiproofConeSortOrder.packed q batch kind.val pos).val%256) (before : Log) :
    ∃ view,
      (install base).op2 proof i=ok view ∧
      (install base).op6 D hash kind view=
        ok (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val pos))) ∧
      run D hash (Port4B_LeafCode.code kind view) before=
        ok (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val pos)),
          before++[(Port4B_LeafCode.input kind view,
            encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val pos)))]) ∧
      flatten (Port4B_LeafCode.input kind view)=OraclePortSelectedDraft.leaf parsed kind.val pos := by
  obtain ⟨view,read,size,content⟩ := Port4B_Opening.selected proof len parsed wire q batch kind.val pos mem i rebased
  have address : flatten (Port4B_LeafCode.input kind view)=OraclePortSelectedDraft.leaf parsed kind.val pos := by
    rw [Port4B_LeafCode.address,content,MultiproofConeOpeningAdapters.leaf_address]
  have calls := Port4B_LeafCode.native_and_reads D hash H law kind view size before
  rw [address] at calls
  exact ⟨view,read,calls.1,calls.2,address⟩

#print axioms selected_call
end AspisR1.Port4B_LeafInstall
end
