import AspisR1ZeroScannerSdkV1.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1ZeroScannerSourceStepsV1
open AspisR1ZeroScannerSdkV1
abbrev Reply := core.result.Result Unit solana_program_error.ProgramError
def rejected : Reply := .Err solana_program_error.ProgramError.AccountAlreadyInitialized

def scanList : List U8 → Reply
  | [] => .Ok ()
  | b::bs => if b=0#u8 then scanList bs else rejected

theorem tail_body_empty (s : Slice U8) (hs : s.val=[]) :
    tail.require_zero_loop.body s=.ok (.done (.Ok ())) := by
  simp [tail.require_zero_loop.body,core.slice.Slice.is_empty,Slice.length,hs]

theorem tail_body_cons (s : Slice U8) (b : U8) (bs : List U8)
    (hs : s.val=b::bs) :
    tail.require_zero_loop.body s=.ok
      (if b=0#u8 then .cont (s.drop 1#usize) else .done rejected) := by
  have hidx : Slice.index_usize s 0#usize=.ok b := by
    simp [Slice.index_usize,hs]
  have hbound : (1#usize).val ≤ s.length := by simp [Slice.length,hs]
  have hsub : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeFromUsizeSlice U8) s {start:=1#usize}=
      .ok (s.drop 1#usize) := by
    change (if (1#usize).val ≤ s.length then .ok (s.drop 1#usize) else .fail .undef)=_
    exact if_pos hbound
  by_cases hb : b=0#u8
  · simp [tail.require_zero_loop.body,core.slice.Slice.is_empty,Slice.length,hs,hidx,hsub,hb]
  · simp [tail.require_zero_loop.body,core.slice.Slice.is_empty,Slice.length,hs,hidx,hsub,hb,rejected]

theorem tail_drop_cons (s : Slice U8) (b : U8) (bs : List U8)
    (hs : s.val=b::bs) : (s.drop 1#usize).val=bs := by
  simp [Slice.drop,hs]

theorem indexed_body_done (s : Slice U8) (index : Usize)
    (hi : s.val.length ≤ index.val) :
    indexed.require_zero_loop.body s index=.ok (.done (.Ok ())) := by
  have hn : ¬index<Slice.len s := by
    change ¬index.val<(Slice.len s).val
    simpa only [Slice.len_val] using (Nat.not_lt.mpr hi)
  simp only [indexed.require_zero_loop.body,if_neg hn]

theorem indexed_body_step (s : Slice U8) (index : Usize) (b : U8)
    (hi : index.val<s.val.length) (hget : s.val[index.val]?=some b) :
    ∃ next : Usize, next.val=index.val+1 ∧
      indexed.require_zero_loop.body s index=.ok
        (if b=0#u8 then .cont next else .done rejected) := by
  have hmax := Slice.length_ineq s
  have hb : index.val+1 ≤ Usize.max := by omega
  have hs : (index+1#usize : Result Usize) ⦃ next => next.val=index.val+1 ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using
      (show index.val+(1#usize).val ≤ Usize.max by simpa using hb)
  obtain ⟨next,hadd,hnext⟩ := WP.spec_imp_exists hs
  have hguard : index<Slice.len s := by
    change index.val<(Slice.len s).val
    simpa only [Slice.len_val] using hi
  have hidx : Slice.index_usize s index=.ok b := by
    simp only [Slice.index_usize,Slice.getElem?_Usize_eq,hget]
  refine ⟨next,hnext,?_⟩
  by_cases hz : b=0#u8
  · simp [indexed.require_zero_loop.body,hguard,hidx,hadd,hz]
  · simp [indexed.require_zero_loop.body,hguard,hidx,hz,rejected]

theorem drop_cons_at {A : Type} (xs : List A) (n : Nat) (hn : n<xs.length) :
    xs.drop n=xs[n]::xs.drop (n+1) := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons b bs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have h : n<bs.length := by simpa using hn
      simpa only [List.drop_succ_cons,List.getElem_cons_succ,Nat.add_assoc] using ih n h

#print axioms tail_body_empty
#print axioms tail_body_cons
#print axioms indexed_body_done
#print axioms indexed_body_step
#print axioms drop_cons_at
end AspisR1ZeroScannerSourceStepsV1
