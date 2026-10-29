import PV_L2E_HostQuerySafety
set_option autoImplicit false
namespace PV_L2E_QueryMemberTrace
open PV_L2D_QueryScan

inductive Event where
  | whileGuard (index limit : Nat) (live : Bool)
  | boundsGuard (index : Nat) (valid : Bool)
  | read (index : Nat)
  | compare (index : Nat) (equal : Bool)
  deriving DecidableEq

/-- xs is the unconsumed accepted prefix. The original source limit is
`i+xs.length` at every recursive step. No scan of the padded array suffix. -/
def run (x : Nat) : Nat → List Nat → Bool × List Event
  | i,[] => (false,[.whileGuard i i false])
  | i,y::ys =>
    let head := [.whileGuard i (i+(y::ys).length) true,
      .boundsGuard i (decide (i<22)),.read i,.compare i (decide (x=y))]
    if x=y then (true,head)
    else let rest := run x (i+1) ys; (rest.1,head ++ rest.2)

theorem complete (x i : Nat) (ys : List Nat) :
    (run x i ys).1=(member x i ys).1 := by
  induction ys generalizing i with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x=y <;> simp only [run,member,h,↓reduceIte,ih]

def project : Event → List PV_L2D_QueryScan.Event
  | .compare i b => [.compare i b]
  | _ => []

/-- The old scanner observation is a projection of this richer observation;
it did omit source loop/bounds guards and is not a complete native trace. -/
theorem projection (x i : Nat) (ys : List Nat) :
    (run x i ys).2.flatMap project=(member x i ys).2 := by
  induction ys generalizing i with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x=y
    · simp [run,member,h,project]
    · simp [run,member,h,project,ih]

def Safe : Event → Prop
  | .boundsGuard _ b => b=true
  | .read i => i<22
  | _ => True

theorem all_safe (x i : Nat) (ys : List Nat) (cap : i+ys.length≤22) :
    ∀ e∈(run x i ys).2,Safe e := by
  induction ys generalizing i with
  | nil => simp [run,Safe]
  | cons y ys ih =>
    have hi : i<22 := by simp only [List.length_cons] at cap; omega
    have ht := ih (i+1) (by simp only [List.length_cons] at cap; omega)
    by_cases h : x=y <;> simp only [run,h,↓reduceIte]
    · simp [Safe,hi]
    · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc]
      intro e he
      rcases he with rfl|rfl|rfl|rfl|he <;> simp_all [Safe]

#print axioms complete
#print axioms projection
#print axioms all_safe
end PV_L2E_QueryMemberTrace
