import LIB_VCarriers
import NMT_R2_ReachLibrary
import NMT_345Semantic
import NMT_345Validator
import RSL_TX1_345
set_option autoImplicit false
noncomputable section
namespace LIBC_S1
open RSL Aeneas Aeneas.Std
/-- Only a representation equality remains for the final canonical bundle.
No decoder, validator, encoder or semantic dictionary is a parameter. -/
def library (V : VLib) (public : V.Public = LIB_VCarriers.Public) : TX1_345.S1Lib V where
 Statement := NMT_345.Statement
 decodeStatement := NMT_R2_ConcreteS1.decode
 decodeReachesAlloc := NMT_R2_ReachLibrary.reaches
 validateStatement := NMT_R2_PublicLibrary.valid
 encodeCandidate := NMT_R2_ConcreteS1.encode
 semanticPublic := fun s => Eq.mp public.symm (NMT_345Prep.toT5 (NMT_345.semanticValue s))
theorem decoder (V : VLib) (public : V.Public = LIB_VCarriers.Public) (b : Bytes) :
 (library V public).decodeStatement b = NMT_R2_ConcreteS1.decode b := rfl
theorem marker (V : VLib) (public : V.Public = LIB_VCarriers.Public) (b : Slice U8) :
 (library V public).decodeReachesAlloc (b.val.map NMT_345.byte) = NMT_R2_Reach.reaches b :=
 NMT_R2_ReachLibrary.from_native b
theorem validate (V : VLib) (public : V.Public = LIB_VCarriers.Public) (s : NMT_345.Statement) :
 (library V public).validateStatement s = true ↔ NMT_345.validateCall s = .ok (.Ok ()) :=
 NMT_R2_PublicLibrary.valid_iff s
theorem semantic_value (s : NMT_345.Statement) :
 NMT_345Prep.toT5 (NMT_345.semanticValue s) = AspisR1.NJB_SemanticPublic.value (NMT_345Prep.toT7 s) := by
 have h := NMT_345.semantic_value s
 rw [NMT_345.semantic_closed] at h
 have eq := Aeneas.Std.Result.ok.inj h
 simpa using (congrArg NMT_345Prep.toT5 eq).symm
theorem semantic (V : VLib) (public : V.Public = LIB_VCarriers.Public) (s : NMT_345.Statement) :
 Eq.mp public ((library V public).semanticPublic s) =
 AspisR1.NJB_SemanticPublic.value (NMT_345Prep.toT7 s) := by
 simp only [library,Eq.mp_trans,Eq.symm_trans_self,Eq.mp_refl]
 exact semantic_value s
theorem encoding (V : VLib) (public : V.Public = LIB_VCarriers.Public) (s : NMT_345.Statement) :
 (library V public).encodeCandidate s =
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
