import NKI_InitialPrefix
import NDO_JFu_BoundedBuilder
import RPv_FJb_BuilderSelected
import NJB_ArrayCarrier
import NJB_ArrayReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_TermSelected
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
abbrev Claims := Array (Array NQ 29#usize) 3#usize
abbrev Selected := Array NQ 84#usize
abbrev builder := pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31

def expected (claims : Claims) (i : Fin (84#usize).val) : NQ :=
 let row:=claims.val[i.val/28]'(by rw [claims.property];have h:=i.isLt;change i.val<84 at h;change i.val/28<3;omega)
 row.val[i.val%28]'(by rw [row.property];have h:=Nat.mod_lt i.val (by decide : 0<28);change i.val%28<29;omega)

theorem callback (claims : Claims) (i : Usize) (hi : i.val<(84#usize).val) :
 builder.call_mut claims i=ok (expected claims ⟨i.val,hi⟩,claims) := by
 obtain ⟨ri,rc,rv⟩:=UScalar.div_spec i (y:=28#usize) (by decide)
 obtain ⟨ci,cc,cv⟩:=WP.spec_imp_exists (UScalar.rem_spec i (y:=28#usize) (by decide))
 have rb : ri.val<(3#usize).val := by change ri.val=i.val/28 at rv;change i.val<84 at hi;change ri.val<3;omega
 have cb : ci.val<(29#usize).val := by change ci.val=i.val%28 at cv;have h:=Nat.mod_lt i.val (by decide : 0<28);change ci.val<29;omega
 let row : Array NQ 29#usize:=claims.val[ri.val]'(by rw [claims.property];exact rb)
 have readRow : Array.index_usize claims ri=ok row := NJB_ArrayReads.read claims ri rb
 have readCell:=NJB_ArrayReads.read row ci cb
 dsimp only [builder]
 unfold pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
 rw [rc,bind_tc_ok,cc,bind_tc_ok,readRow,bind_tc_ok,readCell,bind_tc_ok]
 simp only [row,expected,rv,cv,show (28#usize).val=28 from rfl]

theorem calls (claims : Claims) (i : Usize) (hi : i.val<(84#usize).val) :
 ∃ q,builder.call_mut claims i=ok (q,claims) := ⟨_,callback claims i hi⟩

/--256 gathers exactly3x28 cells from the original3x29 claims. This proves
its full84cell value and canonical domain, not a fixture or just a length. -/
theorem source (claims : Claims)
 (hc : ∀ row∈claims.val, FIw_ArrayValue.canonical row) :
 ∃ selected : Selected,
 array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy builder field.QM31.ZERO claims=ok selected ∧
 FIw_ArrayValue.canonical selected ∧
 ∀ i,NJB_ArrayCarrier.cell selected i=expected claims i := by
 obtain ⟨selected,run⟩:=JFu_BoundedBuilder.source 84#usize builder claims (calls claims)
 have called : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy builder field.QM31.ZERO claims=ok selected := run
 have values (i : Fin (84#usize).val) : NJB_ArrayCarrier.cell selected i=expected claims i := by
  let u : Usize:=Usize.ofNatCore i.val (lt_trans i.isLt (84#usize).hBounds)
  have hi : u.val<(84#usize).val:=i.isLt
  have actual:=FJb_BuilderSelected.value 84#usize field.QM31.Insts.CoreMarkerCopy builder field.QM31.ZERO claims (calls claims) selected called u hi
  have same:=Prod.mk.inj (Result.ok.inj (actual.symm.trans (callback claims u hi)))
  exact same.1
 refine ⟨selected,called,?_,values⟩
 intro q mem
 obtain ⟨i,hi,hq⟩:=List.mem_iff_getElem.mp mem
 have bound : i<(84#usize).val := by simpa only [selected.property] using hi
 have vi:=values ⟨i,bound⟩
 have eq : q=expected claims ⟨i,bound⟩ := by simpa only [NJB_ArrayCarrier.cell,hq] using vi
 rw [eq]
 unfold expected
 exact hc _ (List.getElem_mem _) _ (List.getElem_mem _)
#print axioms callback
#print axioms calls
#print source
#print axioms source
end AspisR1.NLH_TermSelected
end
