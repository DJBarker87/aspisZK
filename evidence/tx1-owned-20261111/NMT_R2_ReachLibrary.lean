import NMT_R2_ReachWrongLength
import NMT_R2_ConcreteS1
import NMT_R2_InputRoundtrip
set_option autoImplicit false
noncomputable section
namespace NMT_R2_ReachLibrary
open Aeneas Aeneas.Std NMT_345 RSL

def reaches (bytes : Bytes) : Bool :=
 if h : bytes.length = 1880 then NMT_R2_Reach.reaches (NMT_R2_InputSlice.statement bytes h) else false

/-- Source-derived marker field, with exact zero-allocation rejection on wrong
length. It replaces the unproved manual header spelling, not the canonical
revision2 field or its quantifiers. -/
theorem from_native (bytes : Slice U8) : reaches (bytes.val.map byte) = NMT_R2_Reach.reaches bytes := by
 unfold reaches
 by_cases length : bytes.val.length = 1880
 · have mapped : (bytes.val.map byte).length = 1880 := by simpa using length
   rw [dif_pos mapped,NMT_R2_InputRoundtrip.from_native bytes length]
 · have mapped : (bytes.val.map byte).length ≠ 1880 := by simpa using length
   rw [dif_neg mapped,NMT_R2_ReachWrongLength.source bytes length]

def library (V : VLib) (encodePublic : Public → V.Public) :
 NMT_R2.TX1_345.S1Lib (NMT_R2_PublicLibrary.withPublic V encodePublic) :=
 {NMT_R2_ConcreteS1.library V encodePublic with decodeReachesAlloc := reaches}

theorem validated_public (V : VLib) (encodePublic : Public → V.Public) :
 NMT_R2_345.ValidatedPublic (NMT_R2_PublicLibrary.withPublic V encodePublic) (library V encodePublic) := by
 intro st good
 exact NMT_R2_PublicLibrary.semantic_domain st good

theorem source_fold (V : VLib) (encodePublic : Public → V.Public)
 (P : PreparedNew (NMT_R2_PublicLibrary.withPublic V encodePublic)) (allocation : NMT_R2_345.Allocation)
 (child : NMT_R2.TX1_328.Args (NMT_R2_PublicLibrary.withPublic V encodePublic) → Env → Obs (Except ProgramError Bytes))
 (packet : NMT_R2.TX1_328.RowSpec_328 (NMT_R2_PublicLibrary.withPublic V encodePublic) P child) :
 NMT_R2.TX1_345.RowSpec_345 (NMT_R2_PublicLibrary.withPublic V encodePublic) P (library V encodePublic)
  (NMT_R2_345.run (NMT_R2_PublicLibrary.withPublic V encodePublic) (library V encodePublic) allocation child) :=
 NMT_R2_345.source_packet _ P _ (validated_public V encodePublic) allocation child packet
#print axioms from_native
#print axioms validated_public
#print axioms source_fold
end NMT_R2_ReachLibrary
end
