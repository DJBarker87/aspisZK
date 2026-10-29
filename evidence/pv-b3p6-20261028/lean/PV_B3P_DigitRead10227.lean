import PV_B3P_ValueCpsBridge10227
import PV_B3P_Ordered227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

/-- The second deterministic read returns the same value; intervening failure stays. -/
theorem repeated_read_between10 {α β γ : Type} (read : Result α)
    (middle : α → Result β) (finish : β → α → Result γ) :
    (do let x ← read; let y ← middle x; let x' ← read; finish y x') =
    (do let x ← read; let y ← middle x; finish y x) := by
  cases read <;> rfl

theorem ordered_fold_congr10 {α β : Type} (first second : α → β → Result α)
    (h : ∀ state index, first state index=second state index)
    (indices : List β) (initial : α) :
    PV_B3P_Ordered227.fold first indices initial = PV_B3P_Ordered227.fold second indices initial := by
  induction indices generalizing initial with
  | nil => rfl
  | cons index indices ih =>
    simp only [PV_B3P_Ordered227.fold]
    rw [h]
    apply congrArg (fun next => second initial index >>= next)
    funext next
    exact ih next

abbrev DigitRange10 := Array aspis_core.field.QM31 33#usize

def digit_finish10 (range : DigitRange10) (offset : Option Usize) (index : Usize)
    (square original : aspis_core.field.QM31) : Result DigitRange10 := do
  let residual ← aspis_core.field.QM31.sub square original
  let target := match offset with | none => index | some start => Usize.wrapping_add start index
  Array.update range target residual

def digit_source_step10 (values : Array aspis_core.field.QM31 16#usize)
    (offset : Option Usize) (range : DigitRange10) (index : Usize) : Result DigitRange10 := do
  let original ← Array.index_usize values index
  let square ← aspis_core.field.QM31.square original
  let repeated ← Array.index_usize values index
  digit_finish10 range offset index square repeated

def digit_single_step10 (values : Array aspis_core.field.QM31 16#usize)
    (offset : Option Usize) (range : DigitRange10) (index : Usize) : Result DigitRange10 := do
  let original ← Array.index_usize values index
  let square ← aspis_core.field.QM31.square original
  digit_finish10 range offset index square original

theorem digit_read_binding10 (values : Array aspis_core.field.QM31 16#usize)
    (offset : Option Usize) (range : DigitRange10) (index : Usize) :
    digit_source_step10 values offset range index = digit_single_step10 values offset range index :=
  repeated_read_between10 (Array.index_usize values index) aspis_core.field.QM31.square (digit_finish10 range offset index)

theorem digit_fold_read_binding10 (values : Array aspis_core.field.QM31 16#usize)
    (offset : Option Usize) (indices : List Usize) (range : DigitRange10) :
    PV_B3P_Ordered227.fold (digit_source_step10 values offset) indices range =
      PV_B3P_Ordered227.fold (digit_single_step10 values offset) indices range :=
  ordered_fold_congr10 _ _ (digit_read_binding10 values offset) indices range
#print axioms repeated_read_between10
#print axioms ordered_fold_congr10
#print axioms digit_read_binding10
#print axioms digit_fold_read_binding10
end PV_B3P_Binding10227
