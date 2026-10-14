import R1QueryStateList
import R1QueryContinuation

/-! Completion of a table-backed q22 scan on an explicit state path. -/
set_option autoImplicit false
namespace AspisR1.QueryCompletion

open R0C.V3 AspisV8R19.Q22WordScan AspisV8R19.Q22SamplerProgram
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

abbrev State := AspisV8R19.SourceDuplexStep.State

variable {M Cv : Type} {L : Nat}

def readCell (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (s : State) : State :=
  (T (squeezeA p s)).getD (acc (squeezeA p s))

def complete (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (xs : List State) :=
  Q22.scanOut (xs.length - 1) Q22.q0
    (xs.dropLast.map (readCell p T acc)) xs.tail (xs.headD default)

theorem getter_correct (T : Table (Addr L) State) (acc H : Addr L → State)
    (c : Addr L)
    (hT : ∀ a v, T a = some v → v = H a)
    (hmissing : T c = none → acc c = H c) :
    (T c).getD (acc c) = H c := by
  cases hcell : T c with
  | none => simp [hcell, hmissing hcell]
  | some v => simp [hcell, hT c v hcell]

theorem complete_states (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (H : Addr L → State)
    (s : Nat → State) (n : Nat)
    (hcoh : ∀ j < n, readCell p T acc (s j) = H (squeezeA p (s j))) :
    complete p T acc (QueryStateList.states s n) =
      Q22.scanOut n Q22.q0 (QueryStateList.blocks p H s n)
        (QueryStateList.advances s n) (s 0) := by
  have hlen : (QueryStateList.states s n).length - 1 = n := by
    rw [QueryStateList.states_length]
    omega
  have hblocks : (List.range n).map (fun j => readCell p T acc (s j)) =
      QueryStateList.blocks p H s n := by
    rw [QueryStateList.blocks]
    apply List.map_congr_left
    intro j hj
    exact hcoh j (List.mem_range.mp hj)
  rw [complete, hlen, QueryStateList.states_dropLast,
    QueryStateList.states_tail, QueryStateList.states_head, List.map_map]
  rw [hblocks]

#print axioms getter_correct
#print axioms complete_states

end AspisR1.QueryCompletion
