import NLH_WrapperState
import NLH_RustCuts
import NLH_TermSelected
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_WrapperGathers
open Aeneas Aeneas.Std Result FIq_Native NLH_WrapperState
open FIv_NativeArithmetic (NQ)
def stage (claims : Claims) (base : State) (n : Nat) : State :=
 {base with selected := (NJB_ArrayCarrier.array
   (fun j => if j.val < n then selectedCell claims j else NJB_ArrayCarrier.cell base.selected j))}
/-- ONE arbitrary native window, including the complete logical array frame.
K046/K047 exercises std::array::from_fn at one window and its actual store. -/
theorem step (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (claims : Claims)
 (point : Array NQ 10#usize) (c : Challenges) (base : State) (i : Fin 84) :
 NLH_WrapperState.step pub claims point c (.gather i) (stage claims base i.val)=
 ok (.Ok (stage claims base (i.val+1))) := by
 have image : (fun j => if j=i then selectedCell claims i else
     NJB_ArrayCarrier.cell (stage claims base i.val).selected j)=
   (fun j => if j.val < i.val+1 then selectedCell claims j else NJB_ArrayCarrier.cell base.selected j) := by
   funext j
   change (if j=i then selectedCell claims i else
     NJB_ArrayCarrier.cell (NJB_ArrayCarrier.array (fun j => if j.val < i.val then selectedCell claims j else NJB_ArrayCarrier.cell base.selected j)) j)=_
   rw [NJB_ArrayCarrier.cell_array]
   by_cases same : j=i
   · subst j;simp only [if_pos (Nat.lt_succ_self i.val),ite_true]
   · have different : j.val ≠ i.val := by intro h;exact same (Fin.ext h)
     by_cases earlier : j.val < i.val
     · simp only [if_neg same,if_pos earlier,if_pos (show j.val < i.val+1 by omega)]
     · simp only [if_neg same,if_neg earlier,if_neg (show ¬j.val < i.val+1 by omega)]
 change ok (core.result.Result.Ok {stage claims base i.val with selected := NJB_ArrayCarrier.array
   (fun j => if j=i then selectedCell claims i else NJB_ArrayCarrier.cell (stage claims base i.val).selected j)} : core.result.Result State Error)=_
 rw [image]
 rfl
/-- Pure ordinal shape, independent of field values and buffer contents. -/
theorem sequential (n : Nat) : (List.finRange n).map Fin.val=List.range' 0 n := by
 apply List.ext_getElem
 · simp
 · intro i hi hj
   simp

theorem fold (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (claims : Claims)
 (point : Array NQ 10#usize) (c : Challenges) (base : State) (indices : List (Fin 84)) (start : Nat)
 (ordered : indices.map Fin.val=List.range' start indices.length) :
 NLH_RustCuts.Cuts (NLH_WrapperState.step pub claims point c) (indices.map Event.gather)
 (stage claims base start) (ok (.Ok (stage claims base (start+indices.length)))) (indices.map Event.gather) := by
 induction indices generalizing start with
 | nil => simpa only [List.map_nil,List.length_nil,Nat.add_zero] using (NLH_RustCuts.Cuts.nil (step := NLH_WrapperState.step pub claims point c) (stage claims base start))
 | cons i is ih =>
   have orderParts : i.val=start ∧ is.map Fin.val=List.range' (start+1) is.length := by
     simpa only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] using ordered
   have first := step pub claims point c base i
   rw [orderParts.1] at first
   have tail := ih (start+1) orderParts.2
   have finish : start+1+is.length=start+(i::is).length := by simp only [List.length_cons];omega
   rw [finish] at tail
   exact .next first tail

theorem source (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (claims : Claims)
 (point : Array NQ 10#usize) (c : Challenges) (base : State)
 (hc : ∀ row∈claims.val,FIw_ArrayValue.canonical row) :
 ∃ selected,NLH_RustCuts.Cuts (NLH_WrapperState.step pub claims point c)
 ((List.finRange 84).map Event.gather) (stage claims base 0) (ok (.Ok (stage claims base 84))) ((List.finRange 84).map Event.gather) ∧
 FIw_ArrayValue.canonical selected ∧ (stage claims base 84).selected=selected ∧
 array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy NLH_TermSelected.builder field.QM31.ZERO claims=ok selected := by
 obtain ⟨selected,call,canon,values⟩ := NLH_TermSelected.source claims hc
 have cuts := fold pub claims point c base (List.finRange 84) 0 (by simpa only [List.length_finRange] using sequential 84)
 have same : (stage claims base 84).selected=selected := by
   have cells : NJB_ArrayCarrier.cell (stage claims base 84).selected=NJB_ArrayCarrier.cell selected := by
     funext j
     change NJB_ArrayCarrier.cell (NJB_ArrayCarrier.array (fun j => if j.val < 84 then selectedCell claims j else NJB_ArrayCarrier.cell base.selected j)) j=_
     rw [NJB_ArrayCarrier.cell_array,if_pos j.isLt]
     exact (values j).symm
   calc
     (stage claims base 84).selected=NJB_ArrayCarrier.array (NJB_ArrayCarrier.cell (stage claims base 84).selected) := (NJB_ArrayCarrier.array_cell _).symm
     _=NJB_ArrayCarrier.array (NJB_ArrayCarrier.cell selected) := congrArg NJB_ArrayCarrier.array cells
     _=selected := NJB_ArrayCarrier.array_cell _
 exact ⟨selected,by simpa only [List.length_finRange,Nat.zero_add] using cuts,canon,same,call⟩
#print axioms step
#print axioms sequential
#print axioms fold
#print axioms source
end AspisR1.NLH_WrapperGathers
end
