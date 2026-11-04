import NFQ_ZeroSource
import NFQ_ZeroStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFU_ZeroPort
/-- Native pointer displacement i selects precisely this value tail. -/
def tail (bytes : List U8) (i : Nat) : List U8 := bytes.drop i

theorem head (bytes : List U8) (i : Nat) :
    (tail bytes i)[0]? = bytes[i]? := by
  simp only [tail, List.getElem?_drop, Nat.add_zero]

theorem length (bytes : List U8) (i : Nat) :
    (tail bytes i).length = bytes.length - i := by
  exact List.length_drop i bytes

theorem advance (bytes : List U8) (i : Nat) :
    (tail bytes i).drop 1 = tail bytes (i+1) := by
  simp only [tail, List.drop_drop, Nat.add_comm]

/-- The next native suffix and the adapted source index advance together;
the bounded source never wraps its cohort usize. -/
theorem index_advance (i : Usize) (bound : i.val < 4096) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  exact NFQ_ZeroPrimitives.wrap_add i 1#usize (by change i.val+1≤4096; omega)

/-- Reuse the checked complete induction, including every rejected prefix.
The native one-step packet supplies the current-tail read and frame above. -/
theorem source (bytes : Slice U8) (bound : bytes.val.length ≤ 4096) :
    AdapterRw.r1_pool_adapter.owned.require_zero bytes =
      (do let result ← NFQ_ScanReference.zero_ref bytes
          ok (NFQ_ZeroSource.result result)) :=
  NFQ_ZeroSource.source bytes bound
#print axioms head
#print axioms length
#print axioms advance
#print axioms index_advance
#print axioms source
end NFU_ZeroPort
