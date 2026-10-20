import Aeneas
set_option autoImplicit false
namespace AspisR1PaintBlocksPrefixV1

/-- The reverse-order writes match captured mutable-iterator continuations. -/
def paint {A : Type} (block : Nat → List A) (k : Nat) : Nat → List A → List A
  | 0,src => src
  | n+1,src => paint block k n (src.setSlice! (k*n) (block n))

/-- Reuses the take/drop/setSlice proof shape from R144BeforeOodBytesBridge. -/
theorem drop_setSlice_at {A : Type} (src replacement : List A) (start : Nat)
    (hfit : start+replacement.length ≤ src.length) :
    (src.setSlice! start replacement).drop start = replacement ++ src.drop (start+replacement.length) := by
  have hstart : start ≤ src.length := by omega
  have hmin : min replacement.length (src.length-start)=replacement.length := by omega
  unfold List.setSlice!
  simp only [hmin,List.take_length,List.drop_append,List.length_append,List.length_take]
  simp [Nat.min_eq_left hstart,List.drop_take]

theorem paint_prefix {A : Type} (block : Nat → List A) (k n : Nat) (src : List A)
    (hfit : k*n ≤ src.length) (hblocks : ∀ i,i<n → (block i).length=k) :
    paint block k n src = (List.range n).flatMap block ++ src.drop (k*n) := by
  induction n generalizing src with
  | zero => simp [paint]
  | succ n ih =>
    have hlen : (block n).length=k := hblocks n (by omega)
    have hprior : k*n ≤ (src.setSlice! (k*n) (block n)).length := by
      rw [List.length_setSlice!]
      exact Nat.le_trans (Nat.mul_le_mul_left k (by omega : n≤n+1)) hfit
    have hnext : k*n+(block n).length ≤ src.length := by
      rw [hlen]
      simpa only [Nat.mul_succ] using hfit
    rw [paint,ih _ hprior (fun i hi => hblocks i (by omega)),drop_setSlice_at _ _ _ hnext]
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    simp only [List.append_assoc,hlen,Nat.mul_succ]

theorem paint_full {A : Type} (block : Nat → List A) (k n : Nat) (src : List A)
    (hsize : src.length=k*n) (hblocks : ∀ i,i<n → (block i).length=k) :
    paint block k n src = (List.range n).flatMap block := by
  rw [paint_prefix block k n src (by omega) hblocks]
  simp only [← hsize,List.drop_length,List.append_nil]

#print axioms drop_setSlice_at
#print axioms paint_prefix
#print axioms paint_full
end AspisR1PaintBlocksPrefixV1
