import Port4B_Opening
import NDO_JFw_Frames
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Opening3
open Aeneas Aeneas.Std Result MultiproofConeCanonical
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes

def value : Slice U8 := JFw_Frames.window 12551 832

theorem length : value.length=832 := JFw_Frames.window_length 12551 832 (by decide)
#print axioms length

theorem source : Port4B_Opening.opening JFx_NativeBytes.proof 3#usize=ok value := by
  obtain ⟨out,run,size,bytes⟩ := Port4B_Opening.opening_exact JFx_NativeBytes.proof
    (by unfold JFx_NativeBytes.proof;exact JFx_NativeBytes.proofBytes_length) 3#usize (by decide)
  have same : out=value := by
    apply Subtype.ext
    apply MultiproofConeByteEquality.bytes_injective
    have target := JFw_Frames.window_bytes 12551 832
    exact bytes.trans target.symm
  exact same ▸ run
#print axioms source
end AspisR1.JGp_Opening3
end
