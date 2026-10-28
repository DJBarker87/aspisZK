import NBX_FrameComposition
set_option autoImplicit false
namespace NBX_PredicateScan
open Aeneas Aeneas.Std Result
/-- Pure short-circuit predicate fold on arbitrary values; this extends the
byte-specific scan to the u64 capacity predicate without scalar encodings. -/
def run {A : Type} (p : A → Bool) (bad : Bool) : List A → Bool
  | [] => bad
  | x::xs => run p (bad || p x) xs

theorem value {A : Type} (p : A → Bool) (bad : Bool) (xs : List A) :
    run p bad xs = (bad || xs.any p) := by
  induction xs generalizing bad with
  | nil => rfl
  | cons x xs ih => simp only [run,ih,List.any_cons,Bool.or_assoc]

/-- Compatibility with the already-checked byte scan. -/
theorem byte (bad : Bool) (xs : List U8) :
    run (fun b => b != 0#u8) bad xs = NBX_FrameComposition.scan bad xs := by
  rw [value,NBX_FrameComposition.scan_value]

theorem step {A : Type} (p : A → Bool) (bad : Bool) (x : A) (xs : List A) :
    run p bad (x::xs) = run p (bad || p x) xs := by
  rw [value,value]
  simp only [List.any_cons,Bool.or_assoc]

/-- Same original sequence reader, now with the actual capacity predicate. -/
theorem capacity (read : Nat → U64) (start count : Nat) :
    run (fun n : U64 => decide (1048576#u64 < n)) false
      (NBX_FrameComposition.sequenceRows read start count) =
    (List.range count).any (fun k => decide (1048576#u64 < read (start+k))) := by
  rw [value,NBX_FrameComposition.rows_value,List.any_map]
  rfl

#print axioms byte
#print axioms value
#print axioms step
#print axioms capacity
end NBX_PredicateScan
