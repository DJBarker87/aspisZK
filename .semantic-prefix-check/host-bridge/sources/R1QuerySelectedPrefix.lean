import R1QueryTruncation

/-! The unique selected element of a nodup continuation list remains the
selected output after scanning only through its index. -/
set_option autoImplicit false
namespace AspisR1.QuerySelectedPrefix

open R0C.V3 AspisV8R19.Q22WordScan AspisV8R19.Q22SamplerProgram

abbrev State := AspisV8R19.SourceDuplexStep.State

theorem getElem_not_mem_drop {α : Type} (xs : List α) (hxs : xs.Nodup)
    (k : Nat) (hk : k < xs.length) : xs[k]'hk ∉ xs.drop (k + 1) := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
      cases k with
      | zero =>
          intro hmem
          have hnot : x ∉ xs := (List.nodup_cons.mp hxs).1
          apply hnot
          simpa using hmem
      | succ k =>
          have hxs' : xs.Nodup := (List.nodup_cons.mp hxs).2
          have hk' : k < xs.length := by simp at hk; omega
          simpa [Nat.add_assoc] using ih hxs' k hk'

theorem selected_truncate (bs xs : List State) (s : State) (k : Nat)
    (hx : xs.Nodup) (hlen : xs.length = 8) (hk : k < xs.length)
    (hsel : (Q22.scanOut 8 Q22.q0 bs xs s).2 = xs[k]'hk) :
    Q22.scanOut (k + 1) Q22.q0 (bs.take (k + 1)) (xs.take (k + 1)) s =
      Q22.scanOut 8 Q22.q0 bs xs s := by
  have hk8 : k + 1 ≤ 8 := by omega
  have htail : (Q22.scanOut 8 Q22.q0 bs xs s).2 ∉ xs.drop (k + 1) := by
    rw [hsel]
    exact getElem_not_mem_drop xs hx k hk
  exact AspisR1.QueryTruncation.scanOut_truncate 8 (k + 1)
    Q22.q0 bs xs s hk8 htail

#print axioms selected_truncate

end AspisR1.QuerySelectedPrefix
