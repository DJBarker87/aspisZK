import Lean
import NFY_Part059

set_option autoImplicit false
namespace NGK_NFV_Copy
open Aeneas Aeneas.Std Result

def write {N M : Usize} (a : Array U8 N) (start : Usize) (src : Array U8 M) : Array U8 N :=
  ⟨a.val.setSlice! start.val src.val, by simpa using a.property⟩

/-- The native one-window copy has an exact standard-library value operation. -/
theorem range {N M : Usize} (a : Array U8 N) (start stop : Usize) (src : Array U8 M)
    (ordered : start ≤ stop) (bounded : stop.val ≤ N.val)
    (width : stop.val - start.val = M.val) :
    (do
      let (part, back) ← core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
        a {start:=start, «end»:=stop}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 part src.to_slice
      ok (back copied)) = ok (write a start src) := by
  have fit : M.val ≤ N.val - start.val := by omega
  simp only [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut]
  simp only [Array.to_slice,Slice.length,a.property,ordered,bounded,and_self,ite_true,bind_tc_ok]
  simp [core.slice.Slice.copy_from_slice,Slice.len,Slice.length,Array.to_slice,
    List.slice,List.length_take,List.length_drop,a.property,src.property,width,Nat.min_eq_left fit,
    Array.from_slice,write]
#print axioms range
theorem prefix_copy {N M : Usize} (a : Array U8 N) (src : Array U8 M)
    (bounded : M.val ≤ N.val) :
    (do
      let (part, back) ← core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
        a {«end»:=M}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 part src.to_slice
      ok (back copied)) = ok (write a 0#usize src) := by
  simp only [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut]
  simp [Array.to_slice,Slice.length,a.property,bounded,bind_tc_ok,
    core.slice.Slice.copy_from_slice,Slice.len,List.slice,src.property,
    Nat.min_eq_left bounded,Array.from_slice,write]
#print axioms prefix_copy

theorem suffix {N M : Usize} (a : Array U8 N) (start : Usize) (src : Array U8 M)
    (bounded : start.val ≤ N.val) (width : N.val-start.val=M.val) :
    (do
      let (part, back) ← core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
        a {start:=start}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 part src.to_slice
      ok (back copied)) = ok (write a start src) := by
  simp only [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut]
  simp [Array.to_slice,Slice.length,a.property,bounded,bind_tc_ok,
    core.slice.Slice.copy_from_slice,Slice.len,Slice.drop,src.property,width,
    Array.from_slice,write]
#print axioms suffix
def updateValue {N : Usize} (a : Array U8 N) (i : Usize) (x : U8) : Array U8 N :=
  ⟨a.val.set i.val x, by simpa using a.property⟩

theorem update {N : Usize} (a : Array U8 N) (i : Usize) (x : U8)
    (bounded : i.val < N.val) :
    Array.update a i x = ok (updateValue a i x) := by
  simp [Array.update,updateValue,bounded]
#print axioms update
theorem bind_pair_finish {A B C D E : Type} (r : Result (A × B))
    (f : A → B → Result C) (g : A → B → C → D) (k : D → Result E) :
    ((do let (a,b) ← r; let c ← f a b; ok (g a b c)) >>= k) =
      (do let (a,b) ← r; let c ← f a b; k (g a b c)) := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨a,b⟩
    change ((f a b >>= fun c => ok (g a b c)) >>= k) = (f a b >>= fun c => k (g a b c))
    cases h : f a b <;> simp only [h,bind_tc_ok,bind_tc_fail,bind_tc_div]
#print axioms bind_pair_finish

theorem range_then {R : Type} {N M : Usize} (a : Array U8 N)
    (start stop : Usize) (src : Array U8 M) (ordered : start ≤ stop)
    (bounded : stop.val ≤ N.val) (width : stop.val-start.val=M.val)
    (k : Array U8 N → Result R) :
    (do
      let (part, back) ← core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
        a {start:=start,«end»:=stop}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 part src.to_slice
      k (back copied)) = k (write a start src) := by
  have h := congrArg (fun result => result >>= k) (range a start stop src ordered bounded width)
  simpa only [bind_pair_finish,bind_tc_ok] using h
#print axioms range_then

theorem prefix_then {R : Type} {N M : Usize} (a : Array U8 N) (src : Array U8 M)
    (bounded : M.val ≤ N.val) (k : Array U8 N → Result R) :
    (do
      let (part, back) ← core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8)) a {«end»:=M}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 part src.to_slice
      k (back copied)) = k (write a 0#usize src) := by
  have h := congrArg (fun result => result >>= k) (prefix_copy a src bounded)
  simpa only [bind_pair_finish,bind_tc_ok] using h
#print axioms prefix_then

theorem suffix_then {R : Type} {N M : Usize} (a : Array U8 N) (start : Usize) (src : Array U8 M)
    (bounded : start.val ≤ N.val) (width : N.val-start.val=M.val)
    (k : Array U8 N → Result R) :
    (do
      let (part, back) ← core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8)) a {start:=start}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 part src.to_slice
      k (back copied)) = k (write a start src) := by
  have h := congrArg (fun result => result >>= k) (suffix a start src bounded width)
  simpa only [bind_pair_finish,bind_tc_ok] using h
#print axioms suffix_then
end NGK_NFV_Copy

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
