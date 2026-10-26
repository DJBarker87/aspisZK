import R1Z.PV_L2_RecordCompact
set_option autoImplicit false
namespace R1Z.PV_L2_BoolTrace
open Aeneas Aeneas.Std Result R1Z.PV_L2_Record

/-- Ordered conjunction visits: an earlier false predicate prevents later
comparison visits, including on rejected certificates. -/
def conjunction (site : Nat) : Nat → List Bool → Recorded Bool
  | _,[] => PV_L2_Record.pure true
  | index,b::rest => if b then
      let tail := conjunction site (index+1) rest
      ⟨tail.value,.guard site index 0 true::tail.events⟩
    else ⟨ok false,[.guard site index 0 false]⟩

theorem value (site index : Nat) (predicates : List Bool) :
    (conjunction site index predicates).value =
      ok (predicates.foldr (· && ·) true) := by
  induction predicates generalizing index with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [conjunction,List.foldr_cons,ih] <;> rfl

theorem false_prefix (site index : Nat) (rest : List Bool) :
    (conjunction site index (false::rest)).events = [.guard site index 0 false] := rfl

#print axioms value
#print axioms false_prefix
end R1Z.PV_L2_BoolTrace
