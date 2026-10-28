import NDO_JFo_ResumeNative
import F3U_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_HashBoundary
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- The installed source wrapper still calls the model oracle. No SHA256
compression implementation or numerical realization is asserted here. -/
def dictionary {Hash : Type} (H : Bytes → State)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) : VTop_Stages.aspis_core.digest.Digest32 Hash :=
  {D with digest := fun _ parts => F3U_Oracle.hashv H parts}

theorem call_iff {Hash : Type} (H : Bytes → State)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (parts : SdkC_Source.Parts) (out : SdkC_Source.Digest) :
    (dictionary H D).digest hash parts=ok out ↔ H (flatten parts)=decodeState out := by
  change ok (encodeState (H (flatten parts)))=ok out ↔ _
  constructor
  · intro h
    have eq := congrArg decodeState (Result.ok.inj h)
    exact (state_roundtrip _).symm.trans eq
  · intro h
    rw [h,array_roundtrip]

def proofParts : SdkC_Source.Parts := Array.to_slice (Array.make 1#usize [JFx_NativeBytes.proof])
def publicParts : SdkC_Source.Parts := Array.to_slice (Array.make 1#usize [JFx_NativeBytes.publicInput])
def checksumParts : SdkC_Source.Parts := Array.to_slice (Array.make 2#usize
  [Array.to_slice (Array.make 22#usize
    [85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,58#u8,
     99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8]),
   JFq_Range.segment 0 1736 (by decide)])

def Realizes (H : Bytes → State) : Prop :=
  H (flatten proofParts)=decodeState JFo_AuthBytes.proofHash ∧
  H (flatten publicParts)=decodeState JFo_AuthBytes.publicHash ∧
  H (flatten checksumParts)=decodeState JFo_AuthBytes.checksum

/-- Exact conjunction of missing oracle equations, without assuming digest
success independently from the installed body. This is an equivalence, not
a discharge of Realizes for SHA256. -/
theorem calls_iff {Hash : Type} (H : Bytes → State)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    ((dictionary H D).digest hash proofParts=ok JFo_AuthBytes.proofHash ∧
     (dictionary H D).digest hash publicParts=ok JFo_AuthBytes.publicHash ∧
     (dictionary H D).digest hash checksumParts=ok JFo_AuthBytes.checksum) ↔ Realizes H := by
  exact and_congr (call_iff H D hash _ _) (and_congr (call_iff H D hash _ _) (call_iff H D hash _ _))

#print axioms call_iff
#print axioms calls_iff
end AspisR1.JFn_HashBoundary
end
