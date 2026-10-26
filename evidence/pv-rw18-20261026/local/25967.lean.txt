import R1Z.ProverRw18FieldBytes
import R1Z.ProverRw18CodecGroups
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CanonicalBytes
open Aeneas Aeneas.Std ProverRw18FieldMeaning
open AspisR1.RetainedFieldByteCodec

theorem image (x : Raw) (hx : Canonical x) :
    (ProverRw18QuarticBytes.bytes (full x)).map ProverCommitWordBytes47.rawByte=
      List.ofFn (encodeQM31LE (ProverCommitLimbBytes47.limbs x hx)) := by
  rw [ProverRw18FieldBytes.encoded,ProverRw18CodecGroups.grouped]

theorem field_image (x : K) :
    (ProverRw18QuarticBytes.bytes (full (ProverRw18FieldEncode.encode x))).map
      ProverCommitWordBytes47.rawByte=
        List.ofFn (encodeQM31LE
          (AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x)) := by
  rw [image _ (ProverRw18FieldEncode.canonical x)]
  congr 2

#print axioms image
#print axioms field_image
end R1Z.ProverRw18CanonicalBytes
