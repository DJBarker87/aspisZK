import PV_B3P_ClosureLinks14227
namespace PV_B3Q_OptionEquality
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- Deployed Option<u64> PartialEq: both Some delegates to scalar equality;
both None returns true, unlike discriminants return false. Copy payloads have
no destructor and the shared loans preserve both options. -/
def source_eq (left right : Option U64) : Result Bool :=
 match left,right with
 | some a,some b => .ok (decide (a=b))
 | none,none => .ok true
 | _,_ => .ok false
def model_eq (left right : Option U64) : Result Bool := .ok (decide (left=right))
theorem eq_binding (left right : Option U64) : source_eq left right = model_eq left right := by
 cases left <;> cases right <;> simp only [source_eq,model_eq,Option.some.injEq,reduceCtorEq,decide_true,decide_false]
/-- PartialEq's default ne first calls eq, then negates the returned Bool.
The source port preserves a failing or divergent comparator unchanged. -/
def source_ne {α : Type} (eq : α → α → Result Bool) (left right : α) : Result Bool := do
 let same ← eq left right
 .ok (!same)
def model_ne {α : Type} (eq : α → α → Result Bool) (left right : α) : Result Bool :=
 match eq left right with
 | .ok same => .ok (!same)
 | .fail e => .fail e
 | .div => .div
theorem ne_binding {α : Type} (eq : α → α → Result Bool) (left right : α) :
    source_ne eq left right = model_ne eq left right := by
 unfold source_ne model_ne
 cases eq left right <;> rfl
inductive Body where | option_eq | option_ne
def Signature : Body → Type := fun _ => Option U64 → Option U64 → Result Bool
def source : (body : Body) → Signature body
 | .option_eq => source_eq
 | .option_ne => source_ne source_eq
def model : (body : Body) → Signature body
 | .option_eq => model_eq
 | .option_ne => source_ne model_eq
theorem option_links : PV_B3P_Link_std_dependency_closure14 Signature source model := by
 intro body
 cases body with
 | option_eq => funext left right; exact eq_binding left right
 | option_ne =>
   funext left right
   unfold source model source_ne
   rw [eq_binding]
#print axioms eq_binding
#print axioms ne_binding
#print axioms option_links
end PV_B3Q_OptionEquality
