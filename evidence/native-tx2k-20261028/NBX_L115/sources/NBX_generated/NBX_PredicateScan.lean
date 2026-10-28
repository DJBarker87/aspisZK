import NBX_FrameComposition
set_option autoImplicit false
namespace NBX_PredicateScan
open Aeneas Aeneas.Std Result
/-- Encode an arbitrary pure predicate result into the already-checked byte
scan; no new iterator, callback law or body interpretation is assumed. -/
def bit (b : Bool) : U8 := if b then 1#u8 else 0#u8

def run {A : Type} (p : A → Bool) (bad : Bool) (xs : List A) : Bool :=
  NBX_FrameComposition.scan bad (xs.map (fun x => bit (p x)))

theorem bit_value (b : Bool) : (bit b != 0#u8) = b := by
  cases b <;> rfl

theorem value {A : Type} (p : A → Bool) (bad : Bool) (xs : List A) :
    run p bad xs = (bad || xs.any p) := by
  rw [run,NBX_FrameComposition.scan_value,List.any_map]
  simp only [Function.comp_apply,bit_value]

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

#print axioms bit_value
#print axioms value
#print axioms step
#print axioms capacity
end NBX_PredicateScan
