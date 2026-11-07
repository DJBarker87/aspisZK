import NMT_R2_PublicLibrary
import NMT_R2_DecoderInputs
import NMT_345Encoder
import NMT_345Common
import NMT_R2_345Fold
set_option autoImplicit false
noncomputable section
namespace NMT_R2_ConcreteS1
open Aeneas Aeneas.Std RSL NMT_345

def decode (bytes : Bytes) : Option Statement :=
 if h : bytes.length = 1880 then
  match decodeCall (NMT_R2_InputSlice.statement bytes h) with
  | .ok (.Ok st) => some st
  | _ => none
 else none

def encode (st : Statement) : Option Bytes :=
 match encodeCall (commonValue st).lane_transition.candidate_afterstate with
 | .ok (.Ok candidate) => some (candidate.val.map byte)
 | _ => none

/-- Every345-specific field now names a concrete existing emitted operation.
No free child Ops dictionary or per-input output equality enters the fold.
The decoder allocation-prefix association and total encoder laws are checked
separately before this is used as an actual-body candidate. -/
def library (V : VLib) (encodePublic : Public → V.Public) :
 NMT_R2.TX1_345.S1Lib (NMT_R2_PublicLibrary.withPublic V encodePublic) where
 Statement := Statement
 decodeStatement := decode
 decodeReachesAlloc := NMT_R2_DecoderInputs.firstAllocation
 validateStatement := NMT_R2_PublicLibrary.valid
 encodeCandidate := encode
 semanticPublic := semanticValue

theorem validated_public (V : VLib) (encodePublic : Public → V.Public) :
 NMT_R2_345.ValidatedPublic (NMT_R2_PublicLibrary.withPublic V encodePublic) (library V encodePublic) := by
 intro st good
 exact NMT_R2_PublicLibrary.semantic_domain st good

/-- Complete source-observation fold using the concrete345 library. This has
only the canonical FULL328 child law; the actual-body interpretation transport
still must be installed before candidate status. -/
theorem source_fold (V : VLib) (encodePublic : Public → V.Public)
 (P : PreparedNew (NMT_R2_PublicLibrary.withPublic V encodePublic)) (allocation : NMT_R2_345.Allocation)
 (child : NMT_R2.TX1_328.Args (NMT_R2_PublicLibrary.withPublic V encodePublic) → Env → Obs (Except ProgramError Bytes))
 (packet : NMT_R2.TX1_328.RowSpec_328 (NMT_R2_PublicLibrary.withPublic V encodePublic) P child) :
 NMT_R2.TX1_345.RowSpec_345 (NMT_R2_PublicLibrary.withPublic V encodePublic) P (library V encodePublic)
  (NMT_R2_345.run (NMT_R2_PublicLibrary.withPublic V encodePublic) (library V encodePublic) allocation child) :=
 NMT_R2_345.source_packet _ P _ (validated_public V encodePublic) allocation child packet
#print axioms validated_public
#print axioms source_fold
end NMT_R2_ConcreteS1
end
