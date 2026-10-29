import PV_L2E_ByteWord
set_option autoImplicit false
namespace PV_L2E_ByteDecode
open PV_L2E_ByteWord

def octets (block : Nat → Nat) (i : Nat) : List Nat :=
  [block (4*i),block (4*i+1),block (4*i+2),block (4*i+3)]

def words (block : Nat → Nat) : Nat → Nat → List Nat
  | _,0 => []
  | i,n+1 => packed (octets block i)::words block (i+1) n

inductive Event where
  | loopGuard (index : Nat) (live : Bool)
  | byteGuard (index : Nat) (valid : Bool)
  | readByte (index : Nat)
  | wordGuard (index : Nat) (valid : Bool)
  | writeWord (index : Nat)
  deriving DecidableEq

/-- Bounds checks are retained explicitly. Width is a public array size. -/
def trace (width : Nat) : Nat → Nat → List Event
  | i,0 => [.loopGuard i false]
  | i,n+1 => [.loopGuard i true] ++
      ([4*i,4*i+1,4*i+2,4*i+3].flatMap fun j =>
        [.byteGuard j (decide (j<4*width)),.readByte j]) ++
      [.wordGuard i (decide (i<width)),.writeWord i] ++ trace width (i+1) n

theorem index_safe (i width : Nat) (hi : i<width) :
    ∀ j∈[4*i,4*i+1,4*i+2,4*i+3],j<4*width := by
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  intro j hj
  rcases hj with rfl|rfl|rfl|rfl <;> omega

theorem length (block : Nat → Nat) (i n : Nat) :
    (words block i n).length=n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [words,ih]

theorem word_bound (block : Nat → Nat) (width i : Nat) (hi : i<width)
    (small : ∀ j, j<4*width → block j<256) :
    packed (octets block i)<2^32 := by
  apply (word32 _ (by rfl) ?_).1
  intro b hb
  simp only [octets,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl <;> apply small <;> omega

theorem all_words_bound (block : Nat → Nat) (width i n : Nat)
    (cap : i+n≤width) (small : ∀ j, j<4*width → block j<256) :
    ∀ w∈words block i n,w<2^32 := by
  induction n generalizing i with
  | zero => simp [words]
  | succ n ih =>
    intro w hw
    simp only [words,List.mem_cons] at hw
    rcases hw with rfl|hw
    · exact word_bound block width i (by omega) small
    · exact ih (i+1) (by omega) w hw

/-- The decoder traverses every byte and writes every output word in fixed
order; values do not enter the event sequence. This is the index-loop model,
not an assertion of the native compiler boundary. -/
theorem decoder_trace_independent (width i n : Nat) (a b : Nat → Nat) :
    (words a i n,trace width i n).2=(words b i n,trace width i n).2 := rfl

#print axioms index_safe
#print axioms length
#print axioms word_bound
#print axioms all_words_bound
#print axioms decoder_trace_independent
end PV_L2E_ByteDecode
