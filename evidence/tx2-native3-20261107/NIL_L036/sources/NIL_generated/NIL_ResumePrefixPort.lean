import NIL_ResumePrefixCut
import NIL_ResultCases
import NIL_CursorSub
set_option autoImplicit false
noncomputable section
namespace NIL_ResumePrefixPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1

theorem source {A B H : Type} (f : A → B)
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes proof public1 : Slice U8) (hash : H)
 (reserved : Bool) (left : Usize → U8 → Result (core.result.Result A Fresh.Err))
 (right : Usize → U8 → Result (core.result.Result B Cohort.Err))
 (tail : ∀ end1 next,outer (NIL_Carriers.inner f) (left end1 next)=right end1 next) :
 outer (NIL_Carriers.inner f)
 (NIL_ResumePrefixCut.fresh (NIL_FreshOps.digest d) bytes proof public1 .S2 hash left)=
 NIL_ResumePrefixCut.cohort (CheckpointBytes4Ops.ops reserved) d bytes proof public1 .S2 hash right := by
 unfold NIL_ResumePrefixCut.fresh NIL_ResumePrefixCut.cohort
 simp only [CheckpointBytes4Ops.ops,variant,Port6CK_Header.size_s2,bind_tc_ok]
 by_cases same : Slice.len bytes=1768#usize
 · rw [same]
   simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
   simp only [outer_bind,bind_outer,outer_if,NIL_ResultCases.outer_ite,NIL_ResultCases.outer_prodlet,NIL_HeaderAny.source,NIL_FreshOps.digest,
    NID_ResumeEmission.Slice.Insts.CoreCmpPartialEqArray,AspisR1Stage2.slicePartialEq,
    core.cmp.impls.PartialEqShared.ne,tail,NIL_ResultCases.outer_ok,NIL_ResultCases.inner_err,NIL_ResultCases.checkpoint_error,
    NIL_CursorSub.source 1768#usize 32#usize (by decide),lift,bind_tc_ok]
   repeat' first
    | rfl
    | (apply NIL_ResultCases.bind_congr; intro x)
    | apply NIL_ResultCases.branch_congr
   rcases x with ⟨bad,rest⟩
   cases bad
   · simp only [Bool.false_eq_true,if_false,outer_bind,NIL_ResultCases.outer_ite,
       NIL_ResultCases.outer_ok,NIL_ResultCases.inner_err,NIL_ResultCases.checkpoint_error,tail]
   · rfl
 · have ne : (Slice.len bytes != 1768#usize)=true := by simpa only [bne_iff_ne] using same
   rw [ne]
   rfl
#print axioms source
end NIL_ResumePrefixPort
