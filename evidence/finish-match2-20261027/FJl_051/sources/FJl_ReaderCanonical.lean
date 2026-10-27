import FJl_PowersCanonical
import Tx2N_Fields
import CheckpointBytes4Ops
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_ReaderCanonical
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- Canonicality of the SAME reader scalar follows from its strict decoder,
without assuming a prior encoding equation or model state. -/
theorem read (r out : verifier.Reader) (x : aspis_core.field.wide_exact.WideExact)
    (run : CheckpointBytes3Reader.readE r=ok (.Ok x,out)) :
    AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers x) := by
  unfold CheckpointBytes3Reader.readE at run
  obtain ⟨⟨b,after⟩,hr,run⟩ := OraclePortCkptAbiTry.bind_success _ _ _ run
  obtain ⟨o,hd,run⟩ := OraclePortCkptAbiTry.bind_success _ _ _ run
  rw [CheckpointBytes3EDecode.decode_e_identification (Array.to_slice b) (by exact b.property)] at hd
  cases decoded : FoldedLeafCodec.decodeWide (MultiproofConeCanonical.bytesOf b.val) with
  | none =>
    change ok none=ok o at hd
    cases Result.ok.inj hd
    cases run
  | some value =>
    change ok (some (CheckpointBytes3EDecode.rawE value))=ok o at hd
    cases Result.ok.inj hd
    have pair := Prod.mk.inj (Result.ok.inj run)
    have same := core.result.Result.Ok.inj pair.1
    rw [←same]
    change AspisR1LoopPowers.Canonical
      (Tx2N_Powers.toPowers (CheckpointBytes4ReaderFields.sourceE value))
    exact FJl_PowersCanonical.value _ (Tx2N_Fields.canonical_e value)
#print axioms read
end AspisR1.FJl_ReaderCanonical
end
