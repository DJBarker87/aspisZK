import PV_B3P_ClosureLinks14227
namespace PV_B3Q_ByteArrayEq
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- Value interpretation of raw_eq on initialized [u8;N], whose layout has no
padding. Executing raw_eq/transmute is the retained V370 compiler boundary. -/
def raw_bytes_equal (n : Usize) (left right : Array U8 n) : Bool := decide (left.val = right.val)
def source_eq (n : Usize) (left right : Array U8 n) : Result Bool :=
 .ok (raw_bytes_equal n left right)
def source_ne (n : Usize) (left right : Array U8 n) : Result Bool := do
 let same ← source_eq n left right
 .ok (!same)
inductive Body where | eq | ne
def Signature (n : Usize) : Body → Type := fun _ => Array U8 n → Array U8 n → Result Bool
def source (n : Usize) : (i : Body) → Signature n i
 | .eq => source_eq n
 | .ne => source_ne n
def model (n : Usize) : (i : Body) → Signature n i
 | .eq => fun left right => .ok (decide (left.val = right.val))
 | .ne => fun left right => .ok (decide (left.val ≠ right.val))
theorem specialized_link (n : Usize) : PV_B3P_Link_std_dependency_closure14
    (Signature n) (source n) (model n) := by
 intro body
 cases body with
 | eq => rfl
 | ne =>
   funext left right
   by_cases h : left.val = right.val <;>
     simp only [source,source_ne,source_eq,raw_bytes_equal,model,ne_eq,h,
       decide_true,decide_false,bind_tc_ok,Bool.not_true,Bool.not_false,not_true_eq_false,not_false_eq_true]
theorem no_hidden_array_difference (n : Usize) (left right : Array U8 n)
    (same : source_eq n left right = .ok true) : left = right := by
 apply Subtype.ext
 have h : decide (left.val = right.val) = true := Result.ok.inj same
 exact of_decide_eq_true h
#print axioms specialized_link
#print axioms no_hidden_array_difference
end PV_B3Q_ByteArrayEq
