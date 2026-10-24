import Port3_NativePendingStep

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativePendingLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativePendingBody
abbrev K := aspis_core.field.QM31

def Prefix (weights : Slice K) (raw : alloc.vec.Vec Row) (upto : Nat) : Prop :=
  ∀ j, j<upto → raw.val[j]?=(weights.val[j]?).map Port3_PendingInstall.row

theorem read_lookup (weights : Slice K) (i : Usize) (w : K)
    (bound : i.val<weights.val.length) (read : Slice.index_usize weights i=ok w) :
    weights.val[i.val]?=some w := by
  obtain ⟨q,hq,hvalue⟩ := WP.spec_imp_exists (Slice.index_usize_spec weights i bound)
  have same := Result.ok.inj (hq.symm.trans read)
  subst q
  rw [List.getElem?_eq_getElem bound]
  exact congrArg some hvalue.symm

theorem complete (weights : Slice K) (raw : alloc.vec.Vec Row)
    (wsize : weights.val.length=64) (rsize : raw.val.length=64)
    (correct : Prefix weights raw 64) : raw.val=weights.val.map Port3_PendingInstall.row := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map]
  by_cases hi : j<64
  · exact correct j hi
  · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
    rfl

theorem write_prefix (weights : Slice K) (raw : alloc.vec.Vec Row) (index : Usize) (w : K)
    (wsize : weights.val.length=64) (rsize : raw.val.length=64) (active : index.val<64)
    (correct : Prefix weights raw index.val) (read : Slice.index_usize weights index=ok w) :
    Prefix weights (raw.set index (Port3_PendingInstall.row w)) (index.val+1) := by
  intro j hj
  change (raw.val.set index.val (Port3_PendingInstall.row w))[j]?=_
  by_cases same : index.val=j
  · subst j
    rw [List.getElem?_set_self (by omega),read_lookup weights index w (by omega) read]
    rfl
  · rw [List.getElem?_set_ne same]
    exact correct j (by omega)

theorem run_total (weights : Slice K) (raw : alloc.vec.Vec Row) (index : Usize)
    (fuel : Nat) (wsize : weights.val.length=64) (rsize : raw.val.length=64)
    (span : index.val+fuel=64) (correct : Prefix weights raw index.val) :
    ∃ out, Port3_NativePendingBody.run weights raw index=ok out ∧
      out.val=weights.val.map Port3_PendingInstall.row := by
  induction fuel generalizing raw index with
  | zero =>
    have stopped : index.val=64 := by omega
    have inactive : ¬ index<Slice.len weights := by change ¬index.val<weights.val.length; omega
    refine ⟨raw,?_,complete weights raw wsize rsize ?_⟩
    · unfold Port3_NativePendingBody.run
      rw [Aeneas.Std.loop.eq_def]
      simp only [body,if_neg inactive,bind_tc_ok]
    · simpa only [stopped] using correct
  | succ n ih =>
    have active : index.val<64 := by omega
    obtain ⟨w,read,step⟩ := Port3_NativePendingStep.step weights raw index wsize rsize active
    have next := Port3_Wrapping.increment index (by omega)
    have prefixNext := write_prefix weights raw index w wsize rsize active correct read
    obtain ⟨out,tail,contents⟩ := ih (raw.set index (Port3_PendingInstall.row w))
      (Usize.wrapping_add index 1#usize) (by simpa using rsize) (by omega)
      (by simpa only [next] using prefixNext)
    refine ⟨out,?_,contents⟩
    unfold Port3_NativePendingBody.run at ⊢ tail
    rw [Aeneas.Std.loop.eq_def]
    rw [step,bind_tc_ok]
    exact tail

#print axioms read_lookup
#print axioms complete
#print axioms write_prefix
#print axioms run_total
end AspisR1.Port3_NativePendingLoop
end
