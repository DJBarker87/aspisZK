import LIBB_PoolCarriers
import NFY_Part035
import LIB_Env
set_option autoImplicit false
noncomputable section
namespace LIBB_NullifierBytes
open Aeneas Aeneas.Std
abbrev Digest := Array U32 8#usize
abbrev chunks := AspisS6SourceCodec.DigestContents.chunks
/-- Full little-endian encoding, including noncanonical words. -/
def key (d : Digest) : RSL.B32 :=
 ⟨LIB_Carriers.bytes ⟨chunks d, by
   simp only [chunks, List.length_append]
   have h := (core.num.U32.to_le_bytes (d.val[0]'(by rw [d.property]; decide))).property
   simp only [core.num.U32.to_le_bytes] at h ⊢
   simp⟩, by
   change (NNC_ByteCarriers.host (chunks d)).length = 32
   simp only [NNC_ByteCarriers.host,List.length_map,chunks,List.length_append]
   simp only [show ∀ x : U32, (core.num.U32.to_le_bytes x).val.length = 4 from
     fun x => (core.num.U32.to_le_bytes x).property]
   rfl⟩

theorem injective : Function.Injective key := by
 intro a b same
 apply AspisR1.NFY_JFt_DigestInjective.injective
 have h := congrArg (fun x : RSL.B32 => LIB_Carriers.rawBytes x.bytes) same
 simpa only [key,LIB_Carriers.bytes,LIB_Carriers.rawBytes,
   NMS_R2N_RSLScalars.bytes,NNC_ByteCarriers.native_host] using h

/-- A logical inverse of the byte carrier, not an execution/image law. -/
def digest (b : RSL.B32) : Option Digest :=
 if h : ∃ d, key d = b then some (Classical.choose h) else none

theorem roundtrip (d : Digest) : digest (key d) = some d := by
 unfold digest
 rw [dif_pos ⟨d,rfl⟩]
 congr 1
 exact injective (Classical.choose_spec (show ∃ x, key x = key d from ⟨d,rfl⟩))
#print axioms injective
#print axioms roundtrip
end LIBB_NullifierBytes
end
