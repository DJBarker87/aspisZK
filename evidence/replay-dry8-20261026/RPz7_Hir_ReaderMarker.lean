import RPz7_Hir_GenesisOrigin
import RPz7_Tx2N_Header
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_ReaderMarker
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem resume (reserved : Bool) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (ck proof pub : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D ck proof pub .S2 hash = ok (.Ok (p,a))) :
    Hist_Store.Initialized ck := by
  obtain ⟨magic,reservedBytes,next,iterator,rest,length,read,header,others⟩ :=
    Tx2N_Header.cuts reserved D ck proof pub hash p a success
  have actual := MultiproofConeSlices.prefix_total ck 8#usize (by rw [length]; decide)
  have same := Result.ok.inj (read.symm.trans actual)
  have first := congrArg (fun xs : List U8 => xs[0]?) header
  rw [same] at first
  simp only [MultiproofConeSlices.sub,List.drop_zero,List.getElem?_take] at first
  have first' : ck.val[0]? = some 82#u8 := by simpa using first
  constructor
  · rw [length]; decide
  · simp only [Slice.index_usize,Slice.getElem?_Usize_eq]
    have zero : (0#usize).val = 0 := by scalar_tac
    simpa only [zero,first']

#print axioms resume
end AspisR1.Hir_ReaderMarker
end
