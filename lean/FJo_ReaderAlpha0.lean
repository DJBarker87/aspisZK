import FJo_ReaderGamma
import FJc_ReadSlot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_ReaderAlpha0
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCompactDraft MultiproofConeCanonical
/-- Strict literal alpha0 decode from the SAME successful reader. -/
theorem value (reserved : Bool) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (checkpoint proof pub : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (run : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D checkpoint proof pub .S2 hash=ok (.Ok (p,a)))
    (alpha : aspis_core.field.wide_exact.WideExact) (read : Array.index_usize p.alpha 0#usize=ok alpha) :
    FoldedLeafCodec.decodeWide (slice (bytesOf checkpoint.val) 240 32)=
      some (CheckpointBytes5Output.ofE alpha) := by
  obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D checkpoint proof pub .S2 hash p a run
  obtain ⟨_,_,_,_,_,length,_⟩ := Tx2N_Header.cuts reserved D checkpoint proof pub hash p a run
  have flat := CheckpointBytes4Layout.flat_fields reserved checkpoint p a f length
  have cell := FJc_ReadSlot.slot _ _ _ read
  change p.alpha.val[0]?=some alpha at cell
  rw [f.alpha] at cell
  have sameAlpha : f.alpha0=alpha := by simpa only [Array.make,List.getElem?_cons_zero,Option.some.injEq] using cell
  obtain ⟨v,decoded,same⟩ := flat.alpha0
  rw [←sameAlpha,←same,CheckpointBytes5Output.ofE_source]
  exact decoded
#print axioms value
end AspisR1.FJo_ReaderAlpha0
end
