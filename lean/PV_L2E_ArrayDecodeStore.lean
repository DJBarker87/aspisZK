import PV_L2E_ArrayForward
import PV_L2E_ByteDecode
set_option autoImplicit false
namespace PV_L2E_ArrayDecodeStore
open PV_L2E_ArrayMemory PV_L2E_ArrayForward PV_L2E_ByteDecode

def run (block : Nat → Nat) : Nat → Nat → Memory → Memory
  | _,0,a => a
  | i,n+1,a => run block (i+1) n (store a i (PV_L2E_ByteWord.packed (octets block i)))

theorem frame (block : Nat → Nat) (i n : Nat) (a : Memory) (j : Nat)
    (outside : j < i ∨ i+n≤j) : run block i n a j=a j := by
  induction n generalizing i a with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    rw [ih _ _ (by omega),store_elsewhere a i j _ (by omega)]

/-- Every byte-decoded word is actually stored in its slot. This proves the
array-to-list relation used by later arithmetic, independently of old memory. -/
theorem complete (block : Nat → Nat) (i n : Nat) (a : Memory) :
    slice (run block i n a) i n=words block i n := by
  induction n generalizing i a with
  | zero => rfl
  | succ n ih =>
    simp only [run,slice,words]
    rw [frame block (i+1) n _ i (Or.inl (by omega)),store_here,ih]

theorem output_bounds (block : Nat → Nat) (i n width : Nat) (a : Memory)
    (cap : i+n≤width) (small : ∀ j,j<4*width → block j<256) :
    ∀ w∈slice (run block i n a) i n,w<2^32 := by
  rw [complete]
  exact all_words_bound block width i n cap small

#print axioms frame
#print axioms complete
#print axioms output_bounds
end PV_L2E_ArrayDecodeStore
