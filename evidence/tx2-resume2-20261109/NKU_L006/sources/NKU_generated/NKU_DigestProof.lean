import NKU_Chronology
import NKK_DigestSource
set_option autoImplicit false
noncomputable section
namespace NKU_DigestProof
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
/-- Native digest G with SAME borrowed slices. Its value remains the existing
runtime item. Proof domain57607/public<=1880 must be established by callers. -/
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) : Stage Unit :=
 fun s => do
 let stored ← core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s.frame.checkpoint
   { start := 16#usize, «end» := 48#usize }
 let chunks ← lift (Array.to_slice (Array.make 1#usize [ s.frame.proof ]))
 NKK_DigestSource.model d hash chunks stored (pure (.Ok ((),{s with phase := .publicDigest})))
def source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) : Stage Unit :=
 fun s => do
 let stored ← core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s.frame.checkpoint
   { start := 16#usize, «end» := 48#usize }
 let chunks ← lift (Array.to_slice (Array.make 1#usize [ s.frame.proof ]))
 NKK_DigestSource.source d hash chunks stored (pure (.Ok ((),{s with phase := .publicDigest})))
theorem source_eq_run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) : source d hash s=run d hash s := by
 unfold source run
 apply NKK_LogAlgebra.bind_congr
 intro stored
 apply NKK_LogAlgebra.bind_congr
 intro chunks
 exact NKK_DigestSource.source_eq_model d hash chunks stored _
/-- The entire immutable frame, decoded values, reader and owner survive. -/
theorem frame (s : NKU.State) :
 ({s with phase := .publicDigest} : NKU.State).frame=s.frame ∧
 ({s with phase := .publicDigest} : NKU.State).decoded=s.decoded ∧
 ({s with phase := .publicDigest} : NKU.State).reader=s.reader ∧
 ({s with phase := .publicDigest} : NKU.State).owned=s.owned := ⟨rfl,rfl,rfl,rfl⟩
#print axioms source_eq_run
#print axioms frame
end NKU_DigestProof
