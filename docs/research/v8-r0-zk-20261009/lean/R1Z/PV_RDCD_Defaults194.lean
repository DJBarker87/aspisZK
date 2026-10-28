import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD_Defaults194
open Aeneas Aeneas.Std Result
/-- Deployed Vec::default calls Vec::new. RawVec empty construction is recorded
    separately in the source binding; this is its retained value carrier. -/
def vecDefault (T : Type) : core.default.Default (alloc.vec.Vec T) :=
  ⟨ok (alloc.vec.Vec.new T)⟩
/-- Array Default's literal macro evaluates T::default in left-to-right order. -/
def evaluateDefaults {T : Type} (inst : core.default.Default T) : Nat → Result (List T)
  | 0 => ok []
  | n+1 => do
    let head ← inst.default
    let tail ← evaluateDefaults inst n
    ok (head :: tail)

def emptyVectors (T : Type) (N : Usize) : Array (alloc.vec.Vec T) N :=
  ⟨List.replicate N.val (alloc.vec.Vec.new T), by simp⟩
def arrayDefault (T : Type) (N : Usize) : core.default.Default (Array (alloc.vec.Vec T) N) :=
  ⟨ok (emptyVectors T N)⟩

theorem repeated {T : Type} (inst : core.default.Default T) (value : T)
    (h : inst.default = ok value) (n : Nat) :
    evaluateDefaults inst n = ok (List.replicate n value) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [evaluateDefaults,h,ih,bind_tc_ok,List.replicate_succ]

theorem vector_value (T : Type) : (vecDefault T).default = ok (alloc.vec.Vec.new T) := rfl
theorem vector_empty (T : Type) : (alloc.vec.Vec.new T).val = [] := rfl
theorem array_values (T : Type) (N : Usize) :
    evaluateDefaults (vecDefault T) N.val = ok (emptyVectors T N).val :=
  repeated (vecDefault T) (alloc.vec.Vec.new T) rfl N.val

theorem every_array_element {T : Type} {N : Usize} (i : Nat) (hi : i < N.val) :
    (emptyVectors T N).val[i]? = some (alloc.vec.Vec.new T) := by
  simp [emptyVectors,List.getElem?_replicate,hi]
/-- Only the two emitted array lengths are deployed Default macro instances. -/
theorem array_lengths : (10 : Nat) ≤ 32 ∧ (16 : Nat) ≤ 32 := by decide
#print axioms repeated
#print axioms vector_value
#print axioms vector_empty
#print axioms array_values
#print axioms every_array_element
#print axioms array_lengths
end R1Z.PV_RDCD_Defaults194
