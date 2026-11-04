import NGD_AtShape
import NGD_SemanticSchedule
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_RowPayload
theorem row_cases (row : U8) (valid : row.val<27) : row = 0#u8 ∨ row = 1#u8 ∨ row = 2#u8 ∨ row = 3#u8 ∨ row = 4#u8 ∨ row = 5#u8 ∨ row = 6#u8 ∨ row = 7#u8 ∨ row = 8#u8 ∨ row = 9#u8 ∨ row = 10#u8 ∨ row = 11#u8 ∨ row = 12#u8 ∨ row = 13#u8 ∨ row = 14#u8 ∨ row = 15#u8 ∨ row = 16#u8 ∨ row = 17#u8 ∨ row = 18#u8 ∨ row = 19#u8 ∨ row = 20#u8 ∨ row = 21#u8 ∨ row = 22#u8 ∨ row = 23#u8 ∨ row = 24#u8 ∨ row = 25#u8 ∨ row = 26#u8 := by scalar_tac

theorem present (row : U8) (valid : row.val<27) :
    ∃ tag size, NGD_AtG.shape row = ok (some (tag,size)) := by
  rcases row_cases row valid with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst row
  all_goals exact ⟨_,_,rfl⟩

theorem exact_size (row tag : U8) (size : Usize) (valid : row.val < 27)
    (shape : NGD_AtG.shape row = ok (some (tag,size))) :
    size.val = NFU_PacketDomains.payloadSize row.val := by
  rcases row_cases row valid with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst row
  all_goals simp [NGD_AtG.shape] at shape
  all_goals rcases shape with ⟨rfl,rfl⟩
  all_goals decide

theorem compact_shape (row : U8) :
    NGD_AtG.shape row = AspisS1NativeCompact.r1_wire.row_shape row := by
  rw [← NFQ_RowShape.reference]
  rfl

theorem cursor_bound (row : Nat) (live : row<27) :
    NGD_SemanticSchedule.dst row + 5 + NFU_PacketDomains.payloadSize row ≤ 13831 :=
  (NGD_SemanticSchedule.windows row live).2.1
#print axioms row_cases
#print axioms present
#print axioms exact_size
#print axioms compact_shape
#print axioms cursor_bound
end NGD_RowPayload
