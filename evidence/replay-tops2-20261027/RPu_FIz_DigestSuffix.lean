import RPu_FIz_DigestBinding
import RPu_FIy_PublicDigestSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_DigestSuffix
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
def keys (p : R0P.Public K) : List R0P.DigestKey := [.nextRoot]++
  (if R0P.digestCarry p.nextPairIndex<20 then [.carry] else [])
theorem next (p : Public) (carry : Nat) (h : carry<20) :
    FIw_PublicModel.digest (FIy_PublicDigestSuffix.next p carry)=
      (FIw_PublicModel.ofPublic p).nextFrontier ⟨carry,h⟩ := by
  unfold FIy_PublicDigestSuffix.next FIw_PublicModel.ofPublic
  rw [List.getElem?_eq_getElem (by rw [p.transition.candidate_afterstate.next_frontier.property];exact h)]
  rfl

theorem value (p : Public) (o : Openings) (s : Selectors) (old : Fin 8 → K) :
    FIy_PublicDigestSuffix.model p o s p.transition.live_snapshot old=
      (keys (FIw_PublicModel.ofPublic p)).foldl (fun acc key=>R0P.digestAddBinding acc
        (FIw_PublicModel.selector s (R0P.digestRow (FIw_PublicModel.ofPublic p) key))
        (FIw_PublicModel.openings o).z (R0P.digestStart (FIw_PublicModel.ofPublic p) key)
        (R0P.digestTarget (FIw_PublicModel.ofPublic p) key)) old := by
  unfold FIy_PublicDigestSuffix.model
  rw [FIz_DigestBinding.value s o.z ⟨859,by decide⟩]
  by_cases hc : R0P.digestCarry p.transition.live_snapshot.next_pair_index.val<20
  · rw [if_pos hc,FIz_DigestBinding.value s o.z ⟨(33+R0P.digestCarry p.transition.live_snapshot.next_pair_index.val)*16+11,by have := R0P.digest_carry_le p.transition.live_snapshot.next_pair_index.val;omega⟩]
    simp only [keys,FIw_PublicModel.ofPublic,hc,↓reduceIte,List.cons_append,List.nil_append,
      List.foldl_cons,List.foldl_nil,R0P.digestTarget,R0P.digestStart,R0P.digestRow,if_pos hc]
    rw [next p _ hc]
    simp only [↓reduceDIte,R0P.g2Row,FIw_PublicModel.openings,FIw_PublicModel.ofPublic,
      show (11 : Fin 16).val=11 from rfl,Nat.mul_comm]
    rfl
  · rw [if_neg hc]
    simp only [keys,FIw_PublicModel.ofPublic,hc,↓reduceIte,List.append_nil,List.foldl_cons,List.foldl_nil,
      R0P.digestTarget,R0P.digestStart,R0P.digestRow]
    rfl
#print axioms next
#print axioms value
end AspisR1.FIz_DigestSuffix
end
