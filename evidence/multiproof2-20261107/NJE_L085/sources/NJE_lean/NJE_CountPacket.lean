import NJE_CountLevels
import NJE_CountInit
import NJE_WellFrozen

set_option autoImplicit false
noncomputable section
namespace NJE_CountPacket
open Aeneas Aeneas.Std Result NJA_Multiproof
open AspisR1 OraclePortFrozenOrder MultiproofConeCountPhysical
attribute [local instance] Classical.propDecidable

def source (indices : Slice U32) := multiproof.node_count NJE_WellFrozen.emitted .Two indices

theorem assoc {α β γ : Type} (r : Result α) (f : α → Result β) (g : β → Result γ) :
    (do let b ← (do let a ← r;f a);g b)=(do let a ← r;let b ← f a;g b) := by
 cases r <;> rfl

theorem initial_view (indices : Slice U32) (bound : indices.val.length≤16) :
 cells (NJA_CountDrop.keys (NJE_CountInit.value indices bound)) 0 indices.val.length=
   indices.val.map (fun x : U32 => x.val) := by
 apply List.ext_getElem
 · simp [cells]
 · intro j hj hj'
   have jb : j < indices.val.length := by simpa only [List.length_map] using hj'
   simp only [cells,List.getElem_map,List.getElem_range,Nat.zero_add]
   unfold NJA_CountDrop.keys NJE_CountInit.value
   rw [getElem!_pos _ j (by simp only [List.length_append,List.length_replicate];omega),
     List.getElem_append_left jb]

theorem continuation {α : Type} (indices : Slice U32) (g : Array U32 16#usize → Result α) :
 (do let (part,back) ← core.array.Array.index_mut
       (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
       (Array.repeat 16#usize 0#u32) {«end»:=Slice.len indices}
     let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU32 part indices
     g (back copied))=
 (do let a ← NJE_CountInit.source indices;g a) := by
 unfold NJE_CountInit.source
 cases h : core.array.Array.index_mut
   (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
   (Array.repeat 16#usize 0#u32) {«end»:=Slice.len indices} with
 | ok pair =>
   rcases pair with ⟨part,back⟩
   simp only [bind_tc_ok,assoc]
 | fail e => rfl
 | div => rfl

theorem result (indices : Slice U32) :
 ∃ out : Option Usize, source indices=ok out ∧
   out.map (fun x : Usize => x.val)=
     (if wellFormed (indices.val.map (fun x : U32 => x.val)) then
       some (nodeCount 18 (indices.val.map (fun x : U32 => x.val))) else none) := by
 have well : NJE_WellFrozen.emitted indices=
     ok (decide (wellFormed (indices.val.map (fun x : U32 => x.val)))) := by
   rw [NJE_WellFrozen.association,NJE_WellSource.source,NJA_WellFormed.source_eq]
 by_cases valid : wellFormed (indices.val.map (fun x : U32 => x.val))
 · have bound : indices.val.length≤16 := by simpa using valid.2.1
   let a := NJE_CountInit.value indices bound
   have viewEq : cells (NJA_CountDrop.keys a) 0 (Slice.len indices).val=
       indices.val.map (fun x : U32 => x.val) := by simpa [Slice.len,a] using initial_view indices bound
   obtain ⟨d,exec,value⟩ := NJE_CountLevels.total 18 0#u32 a (Slice.len indices) 0#usize
     (by simp) (by simpa [Slice.len] using bound)
     (by rw [viewEq];exact valid.2.2.1) (by rw [viewEq];exact valid.2.2.2) (by simp)
   refine ⟨some d,?_,?_⟩
   · change multiproof.node_count NJE_WellFrozen.emitted .Two indices=ok (some d)
     unfold multiproof.node_count
     rw [well]
     simp only [valid,decide_true,bind_tc_ok,ite_true]
     simp only [NJA_Arity.two_levels,bind_tc_ok]
     rw [continuation]
     rw [NJE_CountInit.result indices bound]
     simpa only [bind_tc_ok,a,exec]
   · simp only [Option.map_some,if_pos valid]
     apply congrArg Option.some
     rw [viewEq] at value
     simpa only [UScalar.ofNatCore_val_eq,Nat.zero_add] using value
 · refine ⟨none,?_,by simp [valid]⟩
   unfold source multiproof.node_count
   rw [well]
   simp only [valid,decide_false,bind_tc_ok,Bool.false_eq_true,ite_false]

theorem TX1_122 (indices : Slice U32) :
 ∃ out : Option Usize, source indices=ok out ∧
   out.map (fun x : Usize => x.val)=
     (if wellFormed (indices.val.map (fun x : U32 => x.val)) then
       some (nodeCount 18 (indices.val.map (fun x : U32 => x.val))) else none) := result indices

theorem TX2_088 (indices : Slice U32) :
 ∃ out : Option Usize, source indices=ok out ∧
   out.map (fun x : Usize => x.val)=
     (if wellFormed (indices.val.map (fun x : U32 => x.val)) then
       some (nodeCount 18 (indices.val.map (fun x : U32 => x.val))) else none) := result indices

#print continuation
#print axioms continuation
#print initial_view
#print axioms initial_view
#print result
#print axioms result
#print TX1_122
#print axioms TX1_122
#print TX2_088
#print axioms TX2_088
end NJE_CountPacket
end
