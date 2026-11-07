import NLU_ConstructArrays
import NLU_ConstructMisc
import NLU_ConstructChallenges
import NLU_ConstructPoints
import NLU_ConstructTranscript
set_option autoImplicit false
namespace AspisR1.NLU_Construct
open Aeneas Aeneas.Std AspisR1PublicPreparation
theorem value_ext (a b : Value)
 (hr : a.roots=b.roots) (hc : a.challenges=b.challenges) (ha : a.alpha=b.alpha)
 (hcl : a.claims=b.claims) (he : a.extra=b.extra) (hb : a.before_z1=b.before_z1)
 (hs : a.state_before_z0=b.state_before_z0) (hz : a.z=b.z) (ht : a.transcript=b.transcript) : a=b := by
 cases a;cases b
 cases hr;cases hc;cases ha;cases hcl;cases he;cases hb;cases hs;cases hz;cases ht;rfl
/-- One actual constructor value is reassembled from all scalar windows.
This conditional value packet does NOT prove a parent heap, allocator state,
physical Box ownership, hash-carrier transport or native136 root. -/
theorem complete (native : Native) (cut : Cut native) (f : Frame) : (native f).value=f.expected :=
 value_ext _ _ (roots native cut f) (challenges native cut f) (alpha native cut f)
  (claims native cut f) (extra native cut f) (before native cut f) (state native cut f)
  (points native cut f) (transcript native cut f)
#print axioms value_ext
#print axioms complete
set_option pp.proofs false in #print complete
end AspisR1.NLU_Construct
