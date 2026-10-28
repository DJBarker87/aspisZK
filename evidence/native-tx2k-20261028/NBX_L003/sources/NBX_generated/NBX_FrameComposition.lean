import NBU_Audit
set_option autoImplicit false
namespace NBX_FrameComposition
open Aeneas Aeneas.Std Result

/-- A reserved-byte scan has no ambient argument. This recursive value law
is the induction partner of NBX_reserved_iteration on an arbitrary pre-state. -/
def scan (bad : Bool) : List U8 → Bool
  | [] => bad
  | b :: bs => scan (bad || (b != 0#u8)) bs

theorem scan_value (bad : Bool) (bytes : List U8) :
    scan bad bytes = (bad || bytes.any (fun b => b != 0#u8)) := by
  induction bytes generalizing bad with
  | nil => simp [scan]
  | cons b bs ih => simp [scan,ih,Bool.or_assoc]

/-- The same original bytes determine every successive one-window argument,
independently of the accumulator's earlier values. -/
def sequenceRows (read : Nat → U64) (start count : Nat) : List U64 :=
  match count with
  | 0 => []
  | n+1 => read start :: sequenceRows read (start+1) n

theorem rows_value (read : Nat → U64) (start count : Nat) :
    sequenceRows read start count =
      (List.range count).map (fun k => read (start+k)) := by
  induction count generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [sequenceRows,List.range_succ_eq_map,List.map_cons,List.map_map,ih]
    congr 1
    apply List.map_congr_left
    intro k hk
    congr 1
    omega

/-- Reads in a composed sequence depend only on the supplied read function;
no native callback or successful child is assumed by this extensional law. -/
theorem rows_ext (read other : Nat → U64) (start count : Nat)
    (same : ∀ k, start ≤ k → k < start+count → read k = other k) :
    sequenceRows read start count = sequenceRows other start count := by
  rw [rows_value,rows_value]
  apply List.map_congr_left
  intro k hk
  apply same
  · omega
  · have := List.mem_range.mp hk
    omega

/-- A return-data write cannot satisfy a frame that preserves return data.
This is the exact effect mismatch, separate from encoding correctness. -/
theorem return_data_not_framed {Bytes : Type} (old encoded : Bytes)
    (different : old ≠ encoded) : ¬ (encoded = old) := Ne.symm different

#print axioms scan_value
#print axioms rows_value
#print axioms rows_ext
#print axioms return_data_not_framed
end NBX_FrameComposition
