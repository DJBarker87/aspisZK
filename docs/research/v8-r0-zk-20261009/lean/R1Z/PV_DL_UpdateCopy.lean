import R1Z.PV_DL_UpdatePlan
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_UpdateCopy
set_option autoImplicit false

/-- The two cursors advance together, writing one input cell into each
successive destination cell. The original suffix is retained. -/
def cells : List U8 → List U8 → List U8
  | buffer,[] => buffer
  | [],_::_ => []
  | _::buffer,x::input => x::cells buffer input

theorem cells_value (buffer input : List U8) (bound : input.length ≤ buffer.length) :
    cells buffer input=input++buffer.drop input.length := by
  induction input generalizing buffer with
  | nil => simp only [cells,List.length_nil,List.drop_zero,List.nil_append]
  | cons x input ih =>
    cases buffer with
    | nil => simp only [List.length_nil,List.length_cons] at bound;omega
    | cons b buffer =>
      simp only [cells,List.length_cons,List.drop_succ_cons,List.cons_append]
      rw [ih buffer (by simp only [List.length_cons] at bound;omega)]

def loop (buffer : List U8) (pos : Nat) (input : List U8) : List U8 :=
  buffer.take pos++cells (buffer.drop pos) input

theorem copy (buffer input : List U8) (pos : Nat)
    (bound : pos+input.length ≤ buffer.length) :
    loop buffer pos input=PV_DL_UpdatePlan.write buffer pos input := by
  unfold loop PV_DL_UpdatePlan.write
  rw [cells_value _ _ (by simp only [List.length_drop];omega)]
  simp only [List.drop_drop,List.append_assoc]

/-- These are every range and subtraction used in the long-input branch of
both shipped digest_blocks and the owned index formulation. -/
theorem bounds (input : List U8) (pos : Nat) (hp : pos<64)
    (long : 64-pos ≤ input.length) :
    let start := PV_DL_UpdatePlan.start pos
    let full := (input.length-start)/64
    let ending := start+full*64
    start ≤ input.length ∧ ending ≤ input.length ∧ input.length-ending<64 ∧
      (pos≠0 → pos+(input.take (64-pos)).length=64) := by
  dsimp
  have hs : PV_DL_UpdatePlan.start pos ≤ input.length := by
    unfold PV_DL_UpdatePlan.start
    split <;> omega
  have hm := Nat.mod_lt (input.length-PV_DL_UpdatePlan.start pos) (by decide : 0<64)
  have he := Nat.mod_add_div (input.length-PV_DL_UpdatePlan.start pos) 64
  constructor
  · exact hs
  constructor
  · omega
  constructor
  · omega
  · intro hn
    simp only [List.length_take]
    omega

#print axioms cells
#print axioms cells_value
#print axioms loop
#print axioms copy
#print axioms bounds
end R1Z.PV_DL_UpdateCopy
