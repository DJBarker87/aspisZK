import R1DuplexOrder

/-! Symbolic list views of an advance path. State distinctness is derived
from the existing whole-trace non-collision event. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryStateList
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

def states (s : Nat → State) (n : Nat) := (List.range (n + 1)).map s
def advances (s : Nat → State) (n : Nat) := (List.range n).map (fun j => s (j + 1))
def blocks (p : Params M Cv L) (H : Addr L → State) (s : Nat → State) (n : Nat) :=
  (List.range n).map (fun j => H (squeezeA p (s j)))

theorem states_length (s : Nat → State) (n : Nat) : (states s n).length = n + 1 := by
  simp [states]

theorem states_dropLast (s : Nat → State) (n : Nat) :
    (states s n).dropLast = (List.range n).map s := by
  rw [states, List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat]

theorem states_tail (s : Nat → State) (n : Nat) : (states s n).tail = advances s n := by
  simp [states, advances, List.range_succ_eq_map, Function.comp_def]

theorem states_head (s : Nat → State) (n : Nat) : (states s n).headD default = s 0 := by
  simp [states, List.range_succ_eq_map]

theorem advances_take (s : Nat → State) (n k : Nat) (hk : k ≤ n) :
    (advances s n).take k = advances s k := by
  simp only [advances, ← List.map_take, List.take_range, Nat.min_eq_left hk]

theorem blocks_take (p : Params M Cv L) (H : Addr L → State)
    (s : Nat → State) (n k : Nat) (hk : k ≤ n) :
    (blocks p H s n).take k = blocks p H s k := by
  simp only [blocks, ← List.map_take, List.take_range, Nat.min_eq_left hk]

theorem advances_nodup (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State) (n : Nat)
    (hstep : ∀ j < n, s (j + 1) = H (advanceA p (s j)))
    (hread : ∀ j < n, Read tr (advanceA p (s j))) : (advances s n).Nodup := by
  apply (List.nodup_range (n := n)).map_on
  intro i hi j hj heq
  have hi' : i < n := List.mem_range.mp hi
  have hj' : j < n := List.mem_range.mp hj
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim ((DuplexOrder.advanced_ne p H tr Qtot hcons hQ hcoll s n
      hstep hread i j hij hj') heq)
  · exact hij
  · exact False.elim ((DuplexOrder.advanced_ne p H tr Qtot hcons hQ hcoll s n
      hstep hread j i hji hi') heq.symm)

#print axioms states_length
#print axioms states_dropLast
#print axioms states_tail
#print axioms states_head
#print axioms advances_take
#print axioms blocks_take
#print axioms advances_nodup
end AspisR1.QueryStateList
end
