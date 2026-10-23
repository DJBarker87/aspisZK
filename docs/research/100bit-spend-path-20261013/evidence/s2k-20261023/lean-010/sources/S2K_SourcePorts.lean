import S2K_SourceStore

/-! All twenty range-write interpretation ports, on the exact extracted
slice/copy/back operation. Digest encoding and iterator scheduling are separate
from this byte-source port. No external Kani fact is assumed. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.SourcePorts
open FrontierCases SourceStore

def bufferArray (b : Buffer) : Array U8 688#usize := ⟨List.ofFn b, List.length_ofFn⟩
def nodeArray (b : Node) : Array U8 32#usize := ⟨List.ofFn b, List.length_ofFn⟩
def observe (a : Array U8 688#usize) : Buffer := fun i => a.val[i.val]!

def step (level : Nat) (before : Buffer) (node : Node) : Buffer :=
  if h : level < 20 then
    let start := Usize.ofNatCore (48 + 32 * level) (by scalar_tac)
    let stop := Usize.ofNatCore (80 + 32 * level) (by scalar_tac)
    match store (bufferArray before) start stop (nodeArray node) with
    | .ok a => observe a
    | _ => before
  else before

theorem port (level : Nat) (range : level < 20) : Contract step level := by
  intro before node i
  have run := store_exact (bufferArray before)
    (Usize.ofNatCore (48 + 32 * level) (by scalar_tac))
    (Usize.ofNatCore (80 + 32 * level) (by scalar_tac)) (nodeArray node)
    (by change _ ≤ _; omega) (by change _ ≤ _; omega) (by change 80 + 32 * level - (48 + 32 * level) = 32; omega)
  simp only [step, dif_pos range, run, observe]
  split
  next h =>
    have mid := Array.setSlice!_getElem!_middle (bufferArray before)
      (nodeArray node).val (48 + 32 * level) i.val (by simp only [nodeArray, List.length_ofFn, Array.length]; have := i.isLt; omega)
    simpa only [Array.getElem!_Nat_eq, bufferArray, nodeArray, List.getElem!_ofFn node _ (by omega)] using mid
  next h =>
    by_cases early : i.val < 48 + 32 * level
    · have pre := Array.setSlice!_getElem!_prefix (bufferArray before)
        (nodeArray node).val (48 + 32 * level) i.val early
      simpa only [Array.getElem!_Nat_eq, bufferArray, nodeArray, List.getElem!_ofFn before _ i.isLt] using pre
    · have post := Array.setSlice!_getElem!_suffix (bufferArray before)
        (nodeArray node).val (48 + 32 * level) i.val (by simp only [nodeArray, List.length_ofFn, Array.length]; have := i.isLt; omega)
      simpa only [Array.getElem!_Nat_eq, bufferArray, nodeArray, List.getElem!_ofFn before _ i.isLt] using post

theorem level00 : Contract step 0 := port 0 (by omega)
theorem level01 : Contract step 1 := port 1 (by omega)
theorem level02 : Contract step 2 := port 2 (by omega)
theorem level03 : Contract step 3 := port 3 (by omega)
theorem level04 : Contract step 4 := port 4 (by omega)
theorem level05 : Contract step 5 := port 5 (by omega)
theorem level06 : Contract step 6 := port 6 (by omega)
theorem level07 : Contract step 7 := port 7 (by omega)
theorem level08 : Contract step 8 := port 8 (by omega)
theorem level09 : Contract step 9 := port 9 (by omega)
theorem level10 : Contract step 10 := port 10 (by omega)
theorem level11 : Contract step 11 := port 11 (by omega)
theorem level12 : Contract step 12 := port 12 (by omega)
theorem level13 : Contract step 13 := port 13 (by omega)
theorem level14 : Contract step 14 := port 14 (by omega)
theorem level15 : Contract step 15 := port 15 (by omega)
theorem level16 : Contract step 16 := port 16 (by omega)
theorem level17 : Contract step 17 := port 17 (by omega)
theorem level18 : Contract step 18 := port 18 (by omega)
theorem level19 : Contract step 19 := port 19 (by omega)

theorem installed (level : Nat) (range : level < 20) : Contract step level :=
  concrete_cases step level00 level01 level02 level03 level04 level05 level06 level07 level08 level09 level10 level11 level12 level13 level14 level15 level16 level17 level18 level19 level range

#print axioms port
#print axioms level00
#print axioms level01
#print axioms level02
#print axioms level03
#print axioms level04
#print axioms level05
#print axioms level06
#print axioms level07
#print axioms level08
#print axioms level09
#print axioms level10
#print axioms level11
#print axioms level12
#print axioms level13
#print axioms level14
#print axioms level15
#print axioms level16
#print axioms level17
#print axioms level18
#print axioms level19
#print axioms installed
end AspisR1.S2K.SourcePorts
