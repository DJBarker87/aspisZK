import NCE_KeyProducerCuts
import NBJ_NodeCuts

set_option autoImplicit false
namespace AspisR1.NCE_KeyReadCuts
open Aeneas Aeneas.Std Result NCE_OpeningCuts
abbrev Read := Carrier → Array U64 16#usize → Usize →
  Result (U64 × Usize × Array U64 16#usize × Carrier)

/-- ONE native key read and cursor advance, with the actual unchanged key
array AND the SAME complete caller. This is not a final stream equality. -/
def NCE_Native_KeysRead (native : Read) : Prop :=
  ∀ caller keys cursor, cursor.val < 16 →
    native caller keys cursor =
      ok (keys.val[cursor.val]!,Usize.wrapping_add cursor 1#usize,keys,caller)

/-- The selected raw read is the existing emitted array accessor. -/
theorem read_source (native : Read) (cut : NCE_Native_KeysRead native)
    (caller : Carrier) (keys : Array U64 16#usize) (cursor : Usize)
    (bound : cursor.val < 16) :
    native caller keys cursor =
      (do let key ← Array.index_usize keys cursor
          ok (key,Usize.wrapping_add cursor 1#usize,keys,caller)) := by
  rw [cut caller keys cursor bound,NBJ_NodeCuts.array_read keys cursor bound]
  rfl

/-- The source cursor cannot wrap on the actual single-key domain. -/
theorem next_position (native : Read) (cut : NCE_Native_KeysRead native)
    (caller : Carrier) (keys : Array U64 16#usize) (cursor : Usize)
    (bound : cursor.val < 16) :
    ∃ key next, native caller keys cursor = ok (key,next,keys,caller) ∧ next.val = cursor.val+1 := by
  exact ⟨_,_,cut caller keys cursor bound,Port3_Wrapping.increment cursor (by omega)⟩

/-- The SAME actual sorted prefix supplies the raw read. This local value
lemma is consumed only after the native producer/sort has constructed it. -/
theorem prefix_read (keys : Array U64 16#usize) (n : Nat) (positions : List Nat)
    (packed : Nat → U64) (front : keys.val.take n = positions.map packed)
    (small : n ≤ 16) (cursor : Usize) (active : cursor.val < n) :
    keys.val[cursor.val]! = packed (positions[cursor.val]!) := by
  have len : keys.val.length = 16 := keys.property
  have length := congrArg List.length front
  simp only [List.length_take,List.length_map] at length
  rw [len,Nat.min_eq_left small] at length
  have position : cursor.val < positions.length := by omega
  have raw : cursor.val < keys.val.length := by rw [len]; omega
  have read := congrArg (fun xs : List U64 => xs[cursor.val]?) front
  simp only [List.getElem?_take_of_lt active,List.getElem?_map,
    List.getElem?_eq_getElem raw,List.getElem?_eq_getElem position,Option.map_some] at read
  rw [getElem!_pos keys.val cursor.val raw,getElem!_pos positions cursor.val position]
  exact Option.some.inj read

#print axioms read_source
#print axioms next_position
#print axioms prefix_read
end AspisR1.NCE_KeyReadCuts
