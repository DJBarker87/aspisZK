import LIBC_S1
import LIBC_FirstBox
set_option autoImplicit false
noncomputable section
namespace LIBC_S1Sources
open Aeneas Aeneas.Std RSL
/-- Complete CLOSED332 model (outer fail/div and Rust Err included) before
S1's required Option projection. This is at the SAME immutable bytes. -/
theorem decode (b : Bytes) : LIBC_S1.decode b =
 if b.length=1880 then
  match NMT_345.mapOuter
   (NMT_345.mapCore (fun s => NMT_345Dec.fromT8
    (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 s)) NMT_345.fromPE)
   (NFY_NEX_PublicModel.run (LIBC_Bytes.raw b)) with
  | .ok (.Ok st) => some st | _ => none
 else none := by
 unfold LIBC_S1.decode
 split <;> simp only [NMT_345.decode_closed]
theorem validate (s : NMT_345.Statement) : LIBC_S1.valid s =
 match NMT_345.mapOuter (NMT_345.mapCore id NMT_345Dec.fromT13)
  (NFY_NEE_ValidatorOracle.run NFY_NEM_PaymentReached.pay NFY_NEM_LaneReached.lane
   NFY_NEM_LateOracle.late (NMT_345Dec.toT8 s)).1 with
 | .ok (.Ok ()) => true | _ => false := by
 unfold LIBC_S1.valid
 rw [NMT_345.validate_closed]
theorem encode (s : NMT_345.Statement) : LIBC_S1.encode s =
 match NMT_345.mapOuter (NMT_345.mapCore id NMT_345Dec.fromT11)
  (NFY_NBN_EncoderSummary.after AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical
   (NMT_345Dec.toT5 (NMT_345.commonValue s).lane_transition.candidate_afterstate)) with
 | .ok (.Ok candidate) => some (candidate.val.map NMT_345.byte) | _ => none := by
 unfold LIBC_S1.encode
 rw [NMT_345.encode_closed]
/-- F4: the field is the parent's source-fission probe immediately before
the first snapshot Box, not the parent's eventual success bit. -/
theorem allocation (b : Slice U8) (bound : b.val.length ≤ 1880) :
 LIBC_S1.reaches (b.val.map NMT_345.byte)=true ↔
 NMT_R2_Reach.full LIBC_FirstBox.beforeBox b=.div := by
 rw [LIBC_S1.reaches_native b bound]
 exact LIBC_FirstBox.reached b
#print axioms decode
#print axioms validate
#print axioms encode
#print axioms allocation
end LIBC_S1Sources
