import FJk_ActiveMaskValue
import FJk_ActiveMaskRegistry
import FJk_CarrierRead
import FIw_CopyEndpoint
import FIw_WordValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_ActiveValue
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
def indices : List (Fin 64) := List.ofFn id
def step (s : Selectors) (sum : K) (j : Fin 64) :=
  let m := R0P.copyActiveRowMasks j
  if m≠0 then sum+FIv_NativeArray.value s.high j.val*
    R0P.copySelectorMaskSum16 (fun i=>FIv_NativeArray.value s.low i.val) m else sum
def model (s : Selectors) (start : Nat) (seed : K) :=
  (indices.drop start).foldl (step s) seed
attribute [local irreducible] R0P.copyActiveRowMasks R0P.copySelectorMaskSum16
/-- Complete source active-loop VALUE by symbolic64-row suffix induction. -/
theorem loop (n : Nat) (i : Usize) (s : Selectors) (before out : field.QM31)
    (span : i.val+n=64) (hh : canonical s.high) (hl : canonical s.low) (hb : Canon before)
    (run : Selectors.active_literal_loop s before i=ok out) :
    Canon out ∧ decode out=model s i.val (decode before) := by
  induction n generalizing i before with
  | zero =>
    have stop : ¬i<64#usize := by scalar_tac
    rw [Selectors.active_literal_loop,if_neg stop] at run
    cases Result.ok.inj run
    refine ⟨hb,?_⟩
    unfold model
    rw [List.drop_eq_nil_of_le (by simp only [indices,List.length_ofFn];omega)]
    rfl
  | succ n ih =>
    have active : i<64#usize := by scalar_tac
    have hi : i.val<64 := by omega
    rw [Selectors.active_literal_loop,if_pos active] at run
    obtain ⟨mask,rm,run⟩ := FIv_Map.bind_success _ _ _ run
    have mem := FIr_ArrayRead.member constants.ACTIVE_ROW_MASKS i mask rm
    have raw := FJk_CarrierRead.value constants.ACTIVE_ROW_MASKS i mask hi rm
    have maskV : mask.val=R0P.copyActiveRowMasks ⟨i.val,hi⟩ :=
      (congrArg UScalar.val raw).symm.trans (FJk_ActiveMaskRegistry.value ⟨i.val,hi⟩)
    have bound : i.val < indices.length := by simpa only [indices,List.length_ofFn] using hi
    by_cases hmask : (mask != 0#u16)=true
    · rw [if_pos hmask] at run
      simp only [bind_assoc_eq,bind_tc_ok] at run
      obtain ⟨high,rh,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨low,rl,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨prod,rp,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨next,rn,run⟩ := FIv_Map.bind_success _ _ _ run
      dsimp only [bind_tc_ok] at run
      obtain ⟨i',ri,tail⟩ := FIv_Map.bind_success _ _ _ run
      have hv := FIv_NativeArray.canonical s.high i high hh rh
      have lv := FJk_ActiveMaskValue.value s.low mask low hl mem rl
      have pv := FIv_NativeValue.mul high low prod hv lv.1 rp
      have nv := FIv_NativeValue.add before prod next hb pv.1 rn
      have inc : i'.val=i.val+1 := FIw_WordValue.add i 1#usize i' ri
      have rest := ih i' next (by omega) nv.1 tail
      refine ⟨rest.1,?_⟩
      have mn : mask.val≠0 := by
        intro z
        have eq : mask=0#u16 := UScalar.eq_of_val_eq z
        subst mask
        contradiction
      have nz : R0P.copyActiveRowMasks ⟨i.val,hi⟩≠0 := maskV ▸ mn
      rw [rest.2,inc,nv.2,pv.2,lv.2,←FIv_NativeArray.read s.high i high rh,maskV]
      unfold model
      rw [List.drop_eq_getElem_cons bound,List.foldl_cons]
      simp only [indices,List.getElem_ofFn,id_eq,step,if_pos nz]
    · rw [if_neg hmask] at run
      dsimp only [bind_tc_ok] at run
      obtain ⟨i',ri,tail⟩ := FIv_Map.bind_success _ _ _ run
      have inc : i'.val=i.val+1 := FIw_WordValue.add i 1#usize i' ri
      have rest := ih i' before (by omega) hb tail
      have mz : mask=0#u16 := by simpa only [bne_iff_ne,not_not] using hmask
      have zz : R0P.copyActiveRowMasks ⟨i.val,hi⟩=0 := maskV.symm.trans (congrArg UScalar.val mz)
      refine ⟨rest.1,?_⟩
      rw [rest.2,inc]
      unfold model
      rw [List.drop_eq_getElem_cons bound,List.foldl_cons]
      simp only [indices,List.getElem_ofFn,id_eq,step,zz,ne_eq,not_true_eq_false,ite_false]
#print axioms loop
end AspisR1.FJk_ActiveValue
end
