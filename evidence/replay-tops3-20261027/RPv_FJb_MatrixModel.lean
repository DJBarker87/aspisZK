import RPv_FJb_MatrixBlockValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_MatrixModel
open Aeneas Aeneas.Std Result
open FIv_NativeValue (K)
open FIw_ArrayValue (decoded)
open FJb_MatrixGroupStep (State)
abbrev Values := Fin (16#usize).val → K
def sample (v : Values) (n : Nat) : K := if h : n < (16#usize).val then v ⟨n,h⟩ else 0
def block (v : Values) (g : Nat) (j : Fin (16#usize).val) : K :=
  let rows := R0P.poseidonMat4 (fun k=>sample v (4*g+k.val))
  if j.val=4*g+3 then rows 3 else
  if j.val=4*g+2 then rows 2 else
  if j.val=4*g+1 then rows 1 else
  if j.val=4*g then rows 0 else v j

theorem at_value (s : State) (n : Nat) : FIv_NativeArray.value s n=sample (decoded s) n := by
  by_cases h : n < (16#usize).val
  · unfold FIv_NativeArray.value
    rw [List.getElem?_eq_getElem (by simpa only [s.property] using h)]
    simp only [sample,dif_pos h]
    rfl
  · unfold FIv_NativeArray.value
    rw [List.getElem?_eq_none (by simpa only [s.property] using Nat.le_of_not_gt h)]
    simp only [sample,dif_neg h]

theorem model (s : State) (g : Nat) : FJb_MatrixBlock.model s g=block (decoded s) g := by
  have he : FJb_MatrixBlock.input s g=(fun k=>sample (decoded s) (4*g+k.val)) := by
    funext k
    exact at_value s _
  funext j
  unfold FJb_MatrixBlock.model block
  rw [he]
  rfl

def fold : Nat → Nat → Values → Values
  | 0,_,v => v
  | n+1,g,v => fold n (g+1) (block v g)
#print axioms at_value
#print axioms model
end AspisR1.FJb_MatrixModel
end
