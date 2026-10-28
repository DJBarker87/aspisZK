import R1Z.PV_RDB2_NonNull

/-! The deployed shared-slice fold uses an index and an unchecked increment,
not repeated `next` calls. This operational law retains callback failure and
divergence and the complete backing storage, on every length and value. -/
namespace R1Z.PV_RDB2_Fold
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_Pointer

def fold {T S : Type} (f : S → T → Result S) : List T → S → Result S
  | [],acc => ok acc
  | x::xs,acc => do let next ← f acc x; fold f xs next

/-- One read per iteration; the snapshot is never overwritten. The fuel is
the exact number of unconsumed elements, established by `complete`. -/
def run {T S : Type} (f : S → T → Result S) (xs : List T) :
    Nat → Nat → S → Result (S × List T)
  | 0,_,acc => ok (acc,xs)
  | fuel+1,i,acc =>
    if h : i < xs.length then do
      let next ← f acc xs[i]
      run f xs fuel (i+1) next
    else fail .undef

theorem complete {T S : Type} (f : S → T → Result S) (xs : List T)
    (fuel i : Nat) (acc : S) (bound : i+fuel=xs.length) :
    run f xs fuel i acc = (do let out ← fold f (xs.drop i) acc; ok (out,xs)) := by
  induction fuel generalizing i acc with
  | zero =>
    have hn : xs.drop i = [] := List.drop_eq_nil_of_le (by omega)
    simp only [run,hn,fold,bind_tc_ok]
  | succ fuel ih =>
    have hi : i < xs.length := by omega
    rw [run,dif_pos hi,List.drop_eq_getElem_cons hi,fold]
    simp only [bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih (i+1) next (by omega)

theorem initial {T S : Type} (f : S → T → Result S) (xs : List T) (acc : S) :
    run f xs xs.length 0 acc = (do let out ← fold f xs acc; ok (out,xs)) :=
  complete f xs xs.length 0 acc (by omega)

/-- The native unchecked increment never wraps on a nonempty iteration. -/
theorem increment (len i : Nat) (wordLimit : Nat)
    (active : i < len) (bounded : len ≤ wordLimit) : i+1 ≤ wordLimit := by omega

/-- A QM31 word contains four u32 limbs. This is a byte-offset bound, not a
field-element bound, and includes the one-past-end offset. -/
theorem qm31_read_bounds (base len i : Nat)
    (active : i < len) (length : len = 1024)
    (addressBound : base+16*len < 2^64) :
    16*i+16 ≤ 16384 ∧ base+16*i+16 < 2^64 ∧ 16*i < 2^63 := by
  omega

def offset (p : Pointer) (i : Nat) : Pointer := ⟨p.allocation,p.address+16*i⟩

theorem offset_provenance (p : Pointer) (i : Nat) :
    (offset p i).allocation = p.allocation := rfl

theorem offset_alignment (p : Pointer) (i : Nat) (aligned : p.address % 4 = 0) :
    (offset p i).address % 4 = 0 := by
  change (p.address+16*i)%4=0
  omega

theorem length_from_pointers (base len : Nat) :
    ((base+16*len)-base)/16 = len := by omega

#print axioms length_from_pointers
#print axioms complete
#print axioms initial
#print axioms increment
#print axioms qm31_read_bounds
#print axioms offset_provenance
#print axioms offset_alignment
end R1Z.PV_RDB2_Fold
