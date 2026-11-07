import NMX_R3_FrontierReject
import NMX_R3_FrontierWords
set_option autoImplicit false
namespace NMX_R3_FrontierFailure
open Aeneas Aeneas.Std Result NMX_R3_ByteCarrier NMX_R3_FrontierWords
local instance : Inhabited Row := ⟨Array.repeat 8#usize 0#u32⟩

theorem step (t : Slice U8) (next : U64) (cap : t.val.length ≤ 768)
 (extent : 688 ≤ t.val.length) (bad : Nat) (bound : bad < 20)
 (rejected : ¬ At t next bad) (a : Frontier) (i : Usize) (same : i.val = bad) :
 NCV_Reference.decode_frontier_loop.body t next a i = ok (.done (.Err ())) := by
 classical
 by_cases canonical : NMX_R3_DigestPositive.Canonical t (48+32*bad)
 · have vacant : (long next >>> UInt64.ofNat bad) &&& 1 = 0 := by
    by_contra occupied
    exact rejected ⟨canonical, fun h => False.elim (occupied h)⟩
   have different : row t bad ≠ NCV_ArrayFrame.coord NCV_Reference.EMPTY bad := by
    intro equal
    exact rejected ⟨canonical, fun _ => equal⟩
   apply NMX_R3_FrontierReject.vacant_error t next a i (row t bad)
    (NMX_R3_ScalarShift.tag next i) (by omega)
   · intro addr addrval
     have atAddr : NMX_R3_DigestPositive.Canonical t addr.val := by
      simpa only [addrval, same] using canonical
     have call := NMX_R3_DigestPositive.value t addr cap (by omega) atAddr
     simpa only [row, addrval, same] using call
   · exact NMX_R3_ScalarShift.raw next i (by omega)
   · apply (NMX_R3_ScalarShift.mask _).mpr
     rw [NMX_R3_ScalarShift.represented next i (by omega), same]
     exact vacant
   · simpa only [same] using different
 · apply NMX_R3_FrontierReject.digest_error t next a i (by omega)
   intro addr addrval
   have notCanonical : ¬ NMX_R3_DigestPositive.Canonical t addr.val := by
    simpa only [addrval, same] using canonical
   have call := NMX_R3_DigestTotal.value t addr cap (by omega)
   rw [NMX_R3_DigestTotal.outcome, if_neg notCanonical] at call
   exact call
#print axioms step
end NMX_R3_FrontierFailure
