import Port9OR_Bodies
import S2W_DigestExtraction
import OracleProgramLawExt

/-! Pointwise native source interpretation versus a FIXED sampled program.
This is local source probability-law suitability, not the security bound. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Law
open FS AspisV8PairedCommitment
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.OracleFiniteSupport

/-- Existing external hashv primitive, interpreted at H with its fixed failure
policy. The emitted SolanaDigest wrapper is left byte-for-byte unchanged. -/
def hashv (D : VTop_Stages.aspis_core.digest.Digest32 AdapterRw.SolanaDigest)
    (self : AdapterRw.SolanaDigest) (H : Bytes → State) :
    S2W_DigestExtraction.Parts → Result S2W_DigestExtraction.Digest :=
  (Port9OR_Bodies.native D H).digest self

theorem source_primitive (D : VTop_Stages.aspis_core.digest.Digest32 AdapterRw.SolanaDigest)
    (self : AdapterRw.SolanaDigest) (H : Bytes → State)
    (parts : S2W_DigestExtraction.Parts) :
    S2W_DigestExtraction.digest (hashv D self H) self parts=
      (Port9OR_Bodies.native D H).digest self parts :=
  S2W_DigestExtraction.digest_eq_hashv _ _ _

/-- Exact finite-support lazy law of the installed checkpoint reader, for ANY
rational observable of its ordered log AND full return. The finite support is
that of ONE fixed Program. No H-dependent experiment, acceptance conditioning,
agreement test, dropped suffix, query credit, or additional collision term. -/
theorem reader_lazy (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (ck proof pub : Slice U8) (v : VTop_Stages.transport.Variant)
    (hash : Hash)
    (f : View Bytes State (Result (core.result.Result
      (VTop_Stages.verifier.Prepared × VTop_Stages.verifier.Accumulator) VTop_Stages.verifier.Error)) → ℚ) :
    let p := Port9OR_Bodies.reader reserved unwrap D ck proof pub v hash
    let s := support p
    lazyMean p emptyTable f =
      mean (fun H : {a // a ∈ s} → State =>
        let oracle := extend s H default
        f (CheckpointBytes5Inputs.observe
          (Port9OR_Code.trace (VTop_Checkpoint.digest (Port9OR_Bodies.native D oracle)) hash
            (Port8EFF_Bodies.readerCode reserved unwrap ck proof pub v)).1,
          Port6CK_Reader.reader reserved unwrap (Port9OR_Bodies.native D oracle) ck proof pub v hash)) := by
  dsimp only
  rw [← finite_support_oracle_law _ _ (fun _ h => h) default f]
  apply mean_congr
  intro H
  rw [Port9OR_Bodies.reader_effects]

#print axioms source_primitive
#print axioms reader_lazy
end AspisR1.Port9OR_Law
end
