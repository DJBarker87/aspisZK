import NDF_ValidatorRun
import NCO_Search
set_option autoImplicit false
noncomputable section
namespace NDF_ValidatorWindows
open Aeneas Aeneas.Std Result
open AspisR1RecordParser

def window (bytes : Slice U8) (i : Nat) : Slice U8 :=
  ⟨(bytes.val.drop (32*i)).take 32,by
    have h : ((bytes.val.drop (32*i)).take 32).length≤32 := by simp only [List.length_take];omega
    have cap : 32≤Usize.max := by scalar_tac
    omega⟩

def windows (bytes : Slice U8) (stop start : Nat) : List (Slice U8) :=
  (List.range' start (stop-start)).map (window bytes)

def bad (bytes : Slice U8) (i : Nat) : Bool := !LPl_Kit_Bytes.validChunk 8 true (window bytes i).val

def outcome (row : U8) : Option Nat → Result (core.result.Result Unit r1_wire.Error)
  | none => ok (.Ok ())
  | some i => if h : i≤UScalar.cMax .Usize then ok (.Err (.NonCanonical row (UScalar.ofNat i h))) else fail .panic

theorem scan (bytes : Slice U8) (row : U8) (stop : Nat) (start : Usize)
    (cap : stop≤116) (bound : start.val≤stop) :
    NDF_ValidatorRun.scan row start (windows bytes stop start.val) =
      outcome row (NCO_Search.search (bad bytes) stop start.val) := by
  by_cases active : start.val<stop
  · have range : List.range' start.val (stop-start.val) =
        start.val::List.range' (start.val+1) (stop-(start.val+1)) := by
      apply List.range'_eq_cons_iff.mpr
      exact ⟨rfl,by omega,by congr 1⟩
    obtain ⟨next,advance,nextVal⟩ := WP.spec_imp_exists
      (Usize.add_spec (x:=start) (y:=1#usize) (by scalar_tac))
    have one : (1#usize).val=1 := by scalar_tac
    rw [one] at nextVal
    rw [windows,range,List.map_cons,NDF_ValidatorRun.scan,advance,bind_tc_ok,NCO_Search.step _ _ _ active]
    cases valid : LPl_Kit_Bytes.validChunk 8 true (window bytes start.val).val with
    | true =>
      simp only [valid,if_true,bad,Bool.not_true,Bool.false_eq_true,if_false]
      have rest := scan bytes row stop next cap (by omega)
      simpa only [windows,nextVal] using rest
    | false =>
      simp only [valid,Bool.false_eq_true,if_false,bad,Bool.not_false,if_true,outcome]
      have small : start.val≤UScalar.cMax .Usize := by scalar_tac
      rw [dif_pos small]
      congr 3
  · have end1 : stop≤start.val := by omega
    rw [NCO_Search.terminal _ _ _ end1]
    simp only [windows,Nat.sub_eq_zero_of_le end1,List.range'_zero,List.map_nil,NDF_ValidatorRun.scan,outcome]
termination_by stop-start.val

#print axioms scan
end NDF_ValidatorWindows
