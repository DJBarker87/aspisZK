import PCC_LaneReference
import PCF_WordBridge
import PCF_CanonicalWords
import PCF_FirstStub
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_LaneModel

def digest (a b c d e f g h : U32) : PCA.Digest :=
  Vector.ofArray #[PCF_WordBridge.word a,PCF_WordBridge.word b,
    PCF_WordBridge.word c,PCF_WordBridge.word d,PCF_WordBridge.word e,
    PCF_WordBridge.word f,PCF_WordBridge.word g,PCF_WordBridge.word h]

theorem canonical (a b c d e f g h : U32) :
    PCC.canonical (digest a b c d e f g h) =
      decide (PCF_LaneShape.canonical a b c d e f g h) := by
  simp only [PCC.canonical,digest,Vector.toList_ofArray,List.all_cons,List.all_nil,
    PCF_WordBridge.word_value]
  simp only [PCF_LaneShape.canonical, decide_and]
  rfl

theorem complete (a b c d e f g h : U32) (s : PCA.PCA_State) :
    ∃ out : U16,
      PCF_LaneRef.lane_reference a b c d e f g h = ok out ∧
      PCC.laneReference (digest a b c d e f g h) s =
        ⟨s,[],if out.val = 256 then .error (.forest .NonCanonicalDigest)
          else .ok (UInt8.ofNat out.val)⟩ := by
  refine ⟨_, PCF_LaneShape.complete a b c d e f g h, ?_⟩
  unfold PCC.laneReference
  rw [canonical]
  by_cases hc : PCF_LaneShape.canonical a b c d e f g h
  · simp only [hc, decide_true, if_true, digest]
    rw [PCF_LaneValue.low_lane]
    have hm : a.val % 256 % 8 = a.val % 8 := Nat.mod_mod_of_dvd a.val (by decide)
    simp only [Vector.getElem_ofArray, List.getElem_cons_zero, PCF_WordBridge.word_value]
    rw [hm]
    simp only [if_neg (by omega : a.val % 8 ≠ 256)]
  · simp only [hc, decide_false, if_false]
    rfl

#print axioms canonical
#print axioms complete
end PCF_LaneModel
