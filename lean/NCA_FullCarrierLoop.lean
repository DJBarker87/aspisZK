import NCA_FullCarrierRow
set_option autoImplicit false
namespace AspisR1.NCA_FullCarrierLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation PSem_Iterator

structure State where
  logical : Slice U8
  row : U8
  src : Usize
  dst : Usize

def body (input : Slice U8) (s : State) : Result State := do
  let result ← compact.expand_semantic_loop.body nativeValues input (iter s.row)
    (NBR_ProducerBuffers.semanticInitial s.logical) s.src s.dst
  match result with
  | .cont (it,semantic,src,dst) => ok ⟨NCA_FullCarrierRow.restore s.logical semantic,it.start,src,dst⟩
  | .done _ => fail .panic

def run (input : Slice U8) : Nat → State → Result State
  | 0,s => ok s
  | n+1,s => do let next ← body input s;run input n next

/-- Same-carrier induction over the27 row calls. No selected final buffer or
per-step success is supplied; JFw/NBR's proved model steps derive them. The
native association of body, including its full-frame law, remains OPEN. -/
theorem source (input : Slice U8) (inputLength : input.val.length=7015)
    (fuel : Nat) (s : State) (count : s.row.val+fuel=27)
    (full : s.logical.val.length=14759)
    (sourcePos : s.src.val=JFw_Geometry.sourcePos s.row.val)
    (destPos : s.dst.val=JFw_Geometry.destPos s.row.val) :
    ∃ final : State, run input fuel s=ok final ∧
      final.row.val=27 ∧ final.logical.val.length=14759 ∧
      final.src.val=7015 ∧ final.dst.val=13831 ∧
      final.logical.val.drop 13831=s.logical.val.drop 13831 := by
  induction fuel generalizing s with
  | zero =>
    have atEnd : s.row.val=27 := by omega
    refine ⟨s,rfl,atEnd,full,?_,?_,rfl⟩
    · rw [sourcePos,atEnd];rfl
    · rw [destPos,atEnd];rfl
  | succ fuel ih =>
    have bound : s.row.val<27 := by omega
    obtain ⟨nextRow,next⟩ := successor_exists s.row bound
    obtain ⟨tag,size,shape⟩ : ∃ tag size,r1_wire.row_shape s.row=ok (some (tag,size)) := by
      rw [PSem_Shapes.table_shape]
      cases ht : ExtractedRowShape.table s.row with
      | none =>
        have no := (ExtractedRowShape.row_shape_none_iff s.row).mp
          (by rw [ExtractedRowShape.row_shape_eq_table,ht])
        omega
      | some pair => exact ⟨pair.1,pair.2,rfl⟩
    obtain ⟨semantic,nextSrc,nextDst,call,src,dst,restored,len,frame⟩ :=
      NCA_FullCarrierRow.source input s.logical s.row nextRow tag size s.src s.dst
        inputLength full bound next shape sourcePos destPos
    let after : State := ⟨NCA_FullCarrierRow.restore s.logical semantic,nextRow,nextSrc,nextDst⟩
    have step : body input s=ok after := by
      unfold body
      rw [call,bind_tc_ok]
      rfl
    obtain ⟨final,tail,row,length,source,dest,unchanged⟩ :=
      ih after (by change nextRow.val+fuel=27;omega) len src dst
    refine ⟨final,?_,row,length,source,dest,unchanged.trans frame⟩
    rw [run,step,bind_tc_ok]
    exact tail

#print axioms source
end AspisR1.NCA_FullCarrierLoop
