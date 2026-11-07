import NMX_R3_FrontierFailure
import NMX_R3_FrontierPositive
set_option autoImplicit false
namespace NMX_R3_FrontierTotal
open Aeneas Aeneas.Std Result NMX_R3_FrontierWords
attribute [local instance] Classical.propDecidable
local instance : Inhabited Row := ⟨Array.repeat 8#usize 0#u32⟩

noncomputable def outcome (t : Slice U8) (next : U64) : core.result.Result Frontier Unit :=
 if Valid t next then .Ok (target t) else .Err ()

/-- Complete frontier result: every error position and the success result,
from one arbitrary-pre-state step plus symbolic induction. -/
theorem value (t : Slice U8) (next : U64) (cap : t.val.length ≤ 768)
 (extent : 688 ≤ t.val.length) :
 NCV_Reference.decode_frontier t next = ok (outcome t next) := by
 by_cases valid : Valid t next
 · rw [outcome, if_pos valid]
   exact NMX_R3_FrontierPositive.value t next cap extent valid
 · have existsBad : ∃ k, k < 20 ∧ ¬ At t next k := by
    by_contra no
    apply valid
    intro k hk
    by_contra rejected
    exact no ⟨k,hk,rejected⟩
   let bad := Nat.find existsBad
   have found := Nat.find_spec existsBad
   have bound : bad < 20 := found.1
   have rejected : ¬ At t next bad := found.2
   have prior : ∀ j, j < bad → At t next j := by
    intro j hj
    by_contra no
    have minimal : bad ≤ j := Nat.find_min' existsBad ⟨by omega,no⟩
    omega
   rw [outcome, if_neg valid]
   apply NMX_R3_FrontierReject.rejected t next bad bound (target t)
   · intro i hi addr same
     exact field t next cap extent i (by omega) (prior i.val hi) addr same
   · intro i hi
     exact guard t next i (by omega) (prior i.val hi)
   · intro a i same
     exact NMX_R3_FrontierFailure.step t next cap extent bad bound rejected a i same
#print axioms value
end NMX_R3_FrontierTotal
