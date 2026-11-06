import NJN_RoundTrip
import KMX_CopyMeaning
set_option autoImplicit false
namespace NJN_GuardModel
/-- Whole-value reference semantics supplied by the exact KMX value laws.
No allocation, native pointer validity or SDK provenance is asserted here. -/
def copyRange (h : Heap) (g : Guard) (src : Nat → Nat) (start count : Nat) : Heap :=
  let c := h.cells g.cell
  {h with cells := (replace h.cells g.cell {c with bytes := KMX_CopyMeaning.loop src c.bytes start count})}
/-- The complete range law follows from KMX's checked finite induction. -/
theorem copy_range (h : Heap) (g : Guard) (src : Nat → Nat) (start count i : Nat) :
    ((copyRange h g src start count).cells g.cell).bytes i =
      if start ≤ i ∧ i < start + count then src i else (h.cells g.cell).bytes i := by
  simp only [copyRange,selected]
  exact KMX_CopyMeaning.loop_spec src (h.cells g.cell).bytes start count i
/-- Outside payload coordinates are preserved, including prefixes and suffixes. -/
theorem copy_range_outside (h : Heap) (g : Guard) (src : Nat → Nat) (start count i : Nat)
    (outside : i < start ∨ start + count ≤ i) :
    ((copyRange h g src start count).cells g.cell).bytes i = (h.cells g.cell).bytes i := by
  simp only [copyRange,selected]
  exact KMX_CopyMeaning.copy_frame src (h.cells g.cell).bytes start count i outside
/-- All non-selected cells and every ownership/metadata field are framed. -/
theorem copy_range_frame (h : Heap) (g : Guard) (src : Nat → Nat) (start count j : Nat)
    (ne : j ≠ g.cell) :
    (copyRange h g src start count).cells j = h.cells j ∧
    (copyRange h g src start count).accounts = h.accounts ∧
    (copyRange h g src start count).tokens = h.tokens ∧
    (copyRange h g src start count).count = h.count := by
  simp [copyRange,replace,ne]
/-- The unsplit exclusive token and its counter remain live through copying. -/
theorem copy_range_live (h : Heap) (g : Guard) (t : Nat) (src : Nat → Nat)
    (start count : Nat) (live : Live h t g) :
    Live (copyRange h g src start count) t g := by
  simpa [Live,copyRange,replace] using live
/-- Releasing the token retains the entire copied payload, including its frame. -/
theorem copy_range_drop (h : Heap) (g : Guard) (t : Nat) (src : Nat → Nat)
    (start count i : Nat) :
    ((release (copyRange h g src start count) t g).cells g.cell).bytes i =
      if start ≤ i ∧ i < start + count then src i else (h.cells g.cell).bytes i := by
  rw [(drop_payload (copyRange h g src start count) t g.cell g).1]
  exact copy_range h g src start count i
#print axioms copy_range
#print axioms copy_range_outside
#print axioms copy_range_frame
#print axioms copy_range_live
#print axioms copy_range_drop
end NJN_GuardModel
