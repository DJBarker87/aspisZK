import R1Z.PV_CBL_PathJoinValue
import R1Z.PV_CBL_JoinAdapter
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RL_V178
set_option autoImplicit false
/-- Unix control after prefix/verbatim branches have been eliminated. -/
def unixPush (base path : List U8) : List U8 :=
  let needSep := PV_CBL_PathJoinValue.separator base
  let cleared := if path.head?=some PV_CBL_PathJoinValue.slash then [] else base
  let withSep := if path.head?=some PV_CBL_PathJoinValue.slash then cleared else cleared++needSep
  withSep++path
/-- Models the full branch tree with the pinned Unix constants. -/
def branchTree (base path : List U8) : List U8 :=
  let prefixLen := 0
  let verbatim := false
  if prefixLen>0 then base else
    if path.head?=some PV_CBL_PathJoinValue.slash then path else
    if verbatim then [] else base++PV_CBL_PathJoinValue.separator base++path
theorem unix_control (base path : List U8) :
    branchTree base path=PV_CBL_PathJoinValue.join base path := by
  simp [branchTree,PV_CBL_PathJoinValue.join]
theorem contents (base path : List U8) :
    unixPush base path=PV_CBL_PathJoinValue.join base path := by
  unfold unixPush PV_CBL_PathJoinValue.join
  split <;> simp_all
/-- Complete Result at the byte-content boundary; no success-only implication. -/
def nativeResult (base path : List U8) : Result (List U8) := ok (unixPush base path)
theorem complete (base path : List U8) :
    nativeResult base path=ok (PV_CBL_PathJoinValue.join base path) :=
  congrArg Result.ok (contents base path)
theorem asref_result {P : Type} (view : P → Result (List U8)) (base : List U8) (p : P) :
    (do let path ← view p; nativeResult base path) =
    (do let path ← view p; ok (PV_CBL_PathJoinValue.join base path)) := by
  cases h : view p <;> simp only [h,bind_tc_ok,complete] <;> rfl
theorem nonvacuous : nativeResult [] []=ok [] ∧
    nativeResult [97#u8] [98#u8]=ok [97#u8,47#u8,98#u8] ∧
    nativeResult [97#u8] [47#u8]=ok [47#u8] := ⟨rfl,rfl,rfl⟩
#print axioms unix_control
#print axioms contents
#print axioms complete
#print axioms asref_result
#print axioms nonvacuous
end R1Z.PV_RL_V178
