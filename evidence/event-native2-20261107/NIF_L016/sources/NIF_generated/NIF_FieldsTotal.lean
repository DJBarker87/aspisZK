import NIF_FieldDomain
import NFS_CallerDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIF_FieldsTotal
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open OraclePortCompactDraft MultiproofConeCanonical MultiproofConeSlices

theorem callback (base : Ops) (q : Slice U8) (size : q.val.length=832)
 (checked : canonical (slice (bytesOf q.val) 672 128)) (i : Usize) (inside : i.val<4) :
 ∃ value, verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
  (NFS_CallerDomains.ops base) q i=ok (value,q) := by
 let payload := sub q 672#usize 800#usize
 have qbound : (800#usize).val≤q.val.length := by change 800≤q.val.length;omega
 have read := range_total q 672#usize 800#usize (by decide) qbound
 have plen : payload.val.length=128 := by
  rw [sub_length q 672#usize 800#usize (by decide) qbound]
  rfl
 have canonical : canonical (bytesOf payload.val) := by
  rw [bytes_sub]
  exact checked
 obtain ⟨value,returned⟩ := NIF_FieldDomain.read_total payload plen canonical i inside
 refine ⟨FIo_Install.fromE value,?_⟩
 change (do
  let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    q {start:=672#usize,«end»:=800#usize}
  let value ← NFS_ReadCanonical.read s i
  ok (value,q))= _
 rw [read]
 simp only [bind_tc_ok]
 unfold NFS_ReadCanonical.read
 rw [returned]
 rfl

theorem loop_total {T C : Type} (f : core.ops.function.FnMut C Usize T)
 (state : C) (indices : List Usize) (bound : ∀ i∈indices,i.val<4)
 (call : ∀ i,i.val<4→∃ value,f.call_mut state i=ok (value,state)) :
 ∃ values, OraclePortStdBuilder.fromFnLoop f indices state=ok (values,state) ∧ values.length=indices.length := by
 induction indices with
 | nil => exact ⟨[],rfl,rfl⟩
 | cons i rest ih =>
   obtain ⟨value,head⟩:=call i (bound i (by simp))
   obtain ⟨values,tail,size⟩:=ih (fun j mem=>bound j (by simp [mem]))
   exact ⟨value::values,OraclePortStdBuilder.fromFnLoop_cons f i rest state state state value values head tail,by simp [size]⟩

theorem fields (base : Ops) (q : Slice U8) (size : q.val.length=832)
 (checked : canonical (slice (bytesOf q.val) 672 128)) :
 ∃ values, (NFS_CallerDomains.ops base).op0 4#usize
  (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (NFS_CallerDomains.ops base)) q=ok values := by
 let f := verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (NFS_CallerDomains.ops base)
 have bound : ∀ i∈OraclePortStdBuilder.indices 4#usize,i.val<4 := by
  intro i mem
  obtain ⟨j,same⟩:=List.mem_ofFn.mp mem
  subst i
  exact j.isLt
 obtain ⟨values,run,length⟩:=loop_total f q (OraclePortStdBuilder.indices 4#usize) bound
  (callback base q size checked)
 have len : values.length=(4#usize).val := by simpa [OraclePortStdBuilder.indices] using length
 refine ⟨⟨values,len⟩,?_⟩
 change OraclePortStdBuilder.fromFn 4#usize f q=_
 unfold OraclePortStdBuilder.fromFn
 rw [run]
 simp only [bind_tc_ok,dif_pos len]
#print axioms callback
#print axioms loop_total
#print axioms fields
end AspisR1.NIF_FieldsTotal
