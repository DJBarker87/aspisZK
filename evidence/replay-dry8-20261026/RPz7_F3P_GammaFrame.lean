import RPz7_F3P_GammaY
import RPz7_PAln_OpeningDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_GammaFrame
open Aeneas Aeneas.Std OraclePortCompactDraft

theorem frame (p : Parsed) (y1 : Slice U8)
    (physical : MultiproofConeCanonical.bytesOf y1.val=expand 29 (slice p.wire 7031 464)) :
    rowBytes p 27=LengthFrameCodec.frame (MultiproofConeCanonical.bytesOf y1.val) := by
  change framed (expand 29 (slice p.wire 7031 464))=_
  rw [← physical,PAln_OpeningDecode.framed_eq]

#print axioms frame
end AspisR1.F3P_GammaFrame
end
