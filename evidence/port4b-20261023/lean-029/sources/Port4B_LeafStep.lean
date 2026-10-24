import Port4B_LeafInstall

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_LeafStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchCalls (Indices Values)
open MultiproofConeRef

abbrev LoopState := Indices × Values × Usize × Usize
abbrev LoopOut := Indices × Values × Option (core.result.Result Unit verifier.Error)

/-- Literal post-hash native control. The leaf is hashed before deduplication. -/
def post (idx : Indices) (val : Values) (d : Usize) (index : U32)
    (leaf : Array U8 32#usize) (pos : Usize) : Result (ControlFlow LoopState LoopOut) := do
  if d > 0#usize then
    let prev ← lift (Usize.wrapping_sub d 1#usize)
    let same ← Port3_BatchStd.sameIndex idx prev index
    if same then
      let prev ← lift (Usize.wrapping_sub d 1#usize)
      let equal ← Port3_BatchStd.sameLeaf val prev leaf
      if equal then ok (.cont (idx,val,d,pos))
      else ok (.done (idx,val,some (.Err verifier.Error.Merkle)))
    else
      let idx1 ← Array.update idx d index
      let val1 ← Array.update val d leaf
      let d1 ← lift (Usize.wrapping_add d 1#usize)
      ok (.cont (idx1,val1,d1,pos))
  else
    let idx1 ← Array.update idx d index
    let val1 ← Array.update val d leaf
    let d1 ← lift (Usize.wrapping_add d 1#usize)
    ok (.cont (idx1,val1,d1,pos))

def project (s : reference.Scratch) (pos : Usize) : Option reference.Scratch → ControlFlow LoopState LoopOut
  | none => .done (s.idx,s.val,some (.Err verifier.Error.Merkle))
  | some t => .cont (t.idx,t.val,t.n,pos)

theorem predecessor (n : Usize) (positive : 0<n.val) :
    (Usize.wrapping_sub n 1#usize).val=n.val-1 := by
  rw [Usize.wrapping_sub_val_eq]
  have cap : 0<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
  have fit : n.val<UScalar.size .Usize := by rw [UScalar.size_def];exact n.bv.isLt
  change (n.val+(UScalar.size .Usize-1))%UScalar.size .Usize=n.val-1
  rw [show n.val+(UScalar.size .Usize-1)=(n.val-1)+UScalar.size .Usize by omega,
    Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem post_exact (s : reference.Scratch) (index : U32) (leaf : Array U8 32#usize)
    (pos : Usize) (room : s.n.val<16) :
    post s.idx s.val s.n index leaf pos =
      ok (project s pos (MultiproofConeLeafContent.next s index leaf room)) := by
  have ilen : s.idx.val.length=16 := s.idx.property
  have vlen : s.val.val.length=16 := s.val.property
  have writeI : Array.update s.idx s.n index=ok (s.idx.set s.n index) := by
    obtain ⟨out,h,e⟩ := WP.spec_imp_exists (Array.update_spec s.idx s.n index (by simpa using room))
    exact h.trans (congrArg Result.ok e)
  have writeV : Array.update s.val s.n leaf=ok (s.val.set s.n leaf) := by
    obtain ⟨out,h,e⟩ := WP.spec_imp_exists (Array.update_spec s.val s.n leaf (by simpa using room))
    exact h.trans (congrArg Result.ok e)
  have inc : Usize.wrapping_add s.n 1#usize=UScalar.ofNat (s.n.val+1) (by scalar_tac) := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s.n (by omega)
  by_cases positive : 0<s.n.val
  · have prev := predecessor s.n positive
    have readI : Array.index_usize s.idx (Usize.wrapping_sub s.n 1#usize)=ok s.idx.val[s.n.val-1]! := by
      have getI : s.idx.val[s.n.val-1]! = s.idx.val[s.n.val-1]'(by omega) := getElem!_pos _ _ (by omega)
      obtain ⟨value,read,hvalue⟩ := WP.spec_imp_exists
        (Array.index_usize_spec s.idx (Usize.wrapping_sub s.n 1#usize) (by rw [prev];simpa using (show s.n.val-1<16 by omega)))
      have same : value=s.idx.val[s.n.val-1]! := by simpa only [prev,getI] using hvalue
      exact read.trans (congrArg Result.ok same)
    have readV : Array.index_usize s.val (Usize.wrapping_sub s.n 1#usize)=ok s.val.val[s.n.val-1]! := by
      have getV : s.val.val[s.n.val-1]! = s.val.val[s.n.val-1]'(by omega) := getElem!_pos _ _ (by omega)
      obtain ⟨value,read,hvalue⟩ := WP.spec_imp_exists
        (Array.index_usize_spec s.val (Usize.wrapping_sub s.n 1#usize) (by rw [prev];simpa using (show s.n.val-1<16 by omega)))
      have same : value=s.val.val[s.n.val-1]! := by simpa only [prev,getV] using hvalue
      exact read.trans (congrArg Result.ok same)
    have nonempty : s.n > 0#usize := positive
    by_cases same : s.idx.val[s.n.val-1]! = index
    · by_cases equal : s.val.val[s.n.val-1]! = leaf
      · simp only [post,if_pos nonempty,lift,bind_tc_ok,Port3_BatchStd.sameIndex,readI,
          Port3_BatchStd.sameLeaf,readV,same,equal,decide_true,if_true,
          MultiproofConeLeafContent.next,positive,and_self,project]
      · simp only [post,if_pos nonempty,lift,bind_tc_ok,Port3_BatchStd.sameIndex,readI,
          Port3_BatchStd.sameLeaf,readV,same,equal,decide_true,decide_false,if_true,if_false,
          MultiproofConeLeafContent.next,positive,and_self,project]
    · simp only [post,if_pos nonempty,lift,bind_tc_ok,Port3_BatchStd.sameIndex,readI,
        same,decide_false,if_false,writeI,writeV,inc,
        MultiproofConeLeafContent.next,positive,and_false,project]
  · have empty : ¬ s.n > 0#usize := positive
    simp only [post,if_neg empty,MultiproofConeLeafContent.next,positive,false_and,if_false,
      writeI,writeV,inc,lift,bind_tc_ok,project]

/-- Successful and duplicate-rejecting native mutations agree with the actual
extracted P6 insertion, while preserving arbitrary scratch suffix contents. -/
theorem reference_post (s : reference.Scratch) (index : U32) (leaf : Array U8 32#usize)
    (pos : Usize) (room : s.n.val<16) :
    post s.idx s.val s.n index leaf pos =
      (do let out ← reference.leaf_step s index leaf; ok (project s pos out)) := by
  rw [MultiproofConeLeafContent.step_exact s index leaf room,bind_tc_ok]
  exact post_exact s index leaf pos room

#print axioms predecessor
#print axioms post_exact
#print axioms reference_post
end AspisR1.Port4B_LeafStep
end
