import LIB_VCarriers
import NMT_R2_ReachWrongLength
import LIBC_Bytes
import NMT_345Encoder
import NMT_345PublicDomain
import NMT_345Semantic
import NMT_345Validator
import RSL_TX1_345
set_option autoImplicit false
noncomputable section
namespace LIBC_S1
open RSL Aeneas Aeneas.Std
def decode (bytes : Bytes) : Option NMT_345.Statement :=
 if h : bytes.length = 1880 then
  match NMT_345.decodeCall (LIBC_Bytes.raw bytes) with
  | .ok (.Ok st) => some st | _ => none
 else none
def reaches (bytes : Bytes) : Bool :=
 if h : bytes.length = 1880 then NMT_R2_Reach.reaches (LIBC_Bytes.raw bytes) else false
def valid (s : NMT_345.Statement) : Bool :=
 match NMT_345.validateCall s with | .ok (.Ok ()) => true | _ => false
def encode (st : NMT_345.Statement) : Option Bytes :=
 match NMT_345.encodeCall (NMT_345.commonValue st).lane_transition.candidate_afterstate with
 | .ok (.Ok candidate) => some (candidate.val.map NMT_345.byte) | _ => none
theorem reaches_native (bytes : Slice U8) (bound : bytes.val.length ≤ 1880) : reaches (bytes.val.map NMT_345.byte) = NMT_R2_Reach.reaches bytes := by
 have raw : LIBC_Bytes.raw (bytes.val.map NMT_345.byte) = bytes := by
  exact LIBC_Bytes.from_native bytes
 unfold reaches
 by_cases length : bytes.val.length = 1880
 · have mapped : (bytes.val.map NMT_345.byte).length = 1880 := by simpa using length
   rw [dif_pos mapped,raw]
 · have mapped : (bytes.val.map NMT_345.byte).length ≠ 1880 := by simpa using length
   rw [dif_neg mapped,NMT_R2_ReachWrongLength.source bytes length]
theorem valid_iff (s : NMT_345.Statement) : valid s = true ↔ NMT_345.validateCall s = .ok (.Ok ()) := by
 unfold valid
 cases h : NMT_345.validateCall s with
 | fail e => simp | div => simp | ok r => cases r <;> simp
/-- Only a representation equality remains for the final canonical bundle.
No decoder, validator, encoder or semantic dictionary is a parameter. -/
def library (V : VLib) (tyPublic : V.Public = LIB_VCarriers.Public) : TX1_345.S1Lib V where
 Statement := NMT_345.Statement
 decodeStatement := decode
 decodeReachesAlloc := reaches
 validateStatement := valid
 encodeCandidate := encode
 semanticPublic := fun s => Eq.mp tyPublic.symm (NMT_345Prep.toT5 (NMT_345.semanticValue s))
theorem decoder (V : VLib) (tyPublic : V.Public = LIB_VCarriers.Public) (b : Bytes) :
 (library V tyPublic).decodeStatement b = decode b := rfl
theorem marker (V : VLib) (tyPublic : V.Public = LIB_VCarriers.Public) (b : Slice U8) (bound : b.val.length ≤ 1880) :
 (library V tyPublic).decodeReachesAlloc (b.val.map NMT_345.byte) = NMT_R2_Reach.reaches b :=
 reaches_native b bound
theorem validate (V : VLib) (tyPublic : V.Public = LIB_VCarriers.Public) (s : NMT_345.Statement) :
 (library V tyPublic).validateStatement s = true ↔ NMT_345.validateCall s = .ok (.Ok ()) :=
 valid_iff s
theorem semantic_value (s : NMT_345.Statement) :
 NMT_345Prep.toT5 (NMT_345.semanticValue s) = AspisR1.NJB_SemanticPublic.value (NMT_345Prep.toT7 s) := by
 have h := NMT_345.semantic_value s
 rw [NMT_345.semantic_closed] at h
 have eq := Aeneas.Std.Result.ok.inj h
 simpa using (congrArg NMT_345Prep.toT5 eq).symm
theorem semantic (V : VLib) (tyPublic : V.Public = LIB_VCarriers.Public) (s : NMT_345.Statement) :
 Eq.mp tyPublic ((library V tyPublic).semanticPublic s) =
 AspisR1.NJB_SemanticPublic.value (NMT_345Prep.toT7 s) := by
 simp only [library,Eq.mp_trans,Eq.symm_trans_self,Eq.mp_refl]
 exact semantic_value s
theorem encoding (V : VLib) (tyPublic : V.Public = LIB_VCarriers.Public) (s : NMT_345.Statement) :
 (library V tyPublic).encodeCandidate s =
 match NMT_345.encodeCall (NMT_345.commonValue s).lane_transition.candidate_afterstate with
 | .ok (.Ok candidate) => some (candidate.val.map NMT_345.byte)
 | _ => none := rfl
#print axioms decoder
#print axioms marker
#print axioms validate
#print axioms semantic_value
#print axioms semantic
#print axioms encoding
end LIBC_S1
