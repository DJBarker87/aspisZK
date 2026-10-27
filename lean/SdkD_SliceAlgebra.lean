import SdkD_ParserRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_SliceAlgebra
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft

theorem take_drop_take {A : Type} (xs : List A) (offset size bound : Nat)
    (room : offset+size ≤ bound) :
    ((xs.take bound).drop offset).take size = (xs.drop offset).take size := by
  rw [List.drop_take,List.take_take]
  rw [Nat.min_eq_left (by omega)]

theorem root1 (stored : Bytes) (p : Parsed) (success : parse stored = some p) :
    (p.semantic[2]?.getD []).drop 5 = slice p.wire 63 32 := by
  have found := SdkD_ParserRows.row2 (slice p.wire 48 6983) p.semantic
    (SdkD_ParserRows.rows stored p success)
  rw [found]
  unfold slice
  rw [List.drop_take,List.drop_drop,List.drop_take,List.drop_drop,List.take_take]
  rfl

#print axioms take_drop_take
#print axioms root1
end AspisR1.SdkD_SliceAlgebra
end
