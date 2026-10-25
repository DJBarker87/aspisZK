import Port6CK_BodyUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_ScalarRoundtrip
open Aeneas Aeneas.Std AspisR1Stage2
open CheckpointBytes3Namespaces CheckpointBytes4ReaderFields
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec

theorem raw_k (q : RawK) (canonical : Canonical q) :
    CheckpointBytes3KDecode.rawK (exactK q canonical)=q := by
  apply CheckpointBytes3KDecode.raw_ext <;>
    simp only [CheckpointBytes3KDecode.rawK,exactK,Equiv.symm_apply_apply,
      CheckpointBytes3KDecode.rawLimbs,CheckpointBytes3ScalarShape.kWords,
      M31ParserRefinement.valueToU32_val,limbs]

theorem k (q : aspis_core.field.QM31) (canonical : Canonical (toK q)) :
    sourceK (exactK (toK q) canonical)=q := by
  rw [sourceK,raw_k,from_to_k]

theorem e (q : aspis_core.field.wide_exact.WideExact) (canonical : CanonicalWide (toE q)) :
    sourceE (exactE (toE q) canonical)=q := by
  change ({c0:=sourceK (exactK (toK q.c0) canonical.1),c1:=sourceK (exactK (toK q.c1) canonical.2)} : aspis_core.field.wide_exact.WideExact)=q
  rw [k,k]

#print axioms raw_k
#print axioms k
#print axioms e
end AspisR1.Port6CK_ScalarRoundtrip
end
