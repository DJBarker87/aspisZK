/- Namespace port of BuilderAppendArguments: same symbolic proof, actual forest extraction. -/
import R1Z.PV_Src_Forest_PathContent

/-! Actual append-path arguments on the admitted cursor range. -/
set_option autoImplicit false
namespace R1Z.PV_Src_Forest_AppendArguments
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_Src_Forest_DigestArguments PV_Src_Forest_AuxContent PV_Src_Forest_TreeArguments PV_Src_Forest_DigestTotal
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder

theorem output_pair (w : RW) (p : RP) :
    out_pair_r w p = outPairR (wordWitness w) (wordPublic p) := by
  cases hp : p.transfer <;>
    simp only [out_pair_r,outPairR,wordPublic,hp,Bool.false_eq_true,if_false,if_true,
      recipient_digest,change_digest,node_digest,zero_digest]

theorem pair_total (W : RustWitness) (P : RustPublic) : ∃ c, outPairR W P = ok c := by
  unfold outPairR
  split <;> repeat first
    | exact note_total _ _
    | exact node_total _ _
    | apply bind_total
    | intro s

theorem append_total (W : RustWitness) (P : RustPublic) (n : Nat) :
    ∃ c, appCurR W P n = ok c := by
  induction n with
  | zero => exact pair_total W P
  | succ n ih =>
    obtain ⟨c,hc⟩ := ih
    obtain ⟨d,hd⟩ := node_total (orderedR c (appSibR P n) (appBitR P n)).1
      (orderedR c (appSibR P n) (appBitR P n)).2
    exact ⟨d,by rw [appCurR,hc];simp only [bind_tc_ok];exact hd⟩

theorem nonzero (x : U64) : (x != 0#u64) = decide (x.val ≠ 0) := by
  by_cases hx : x = 0#u64
  · rw [hx];rfl
  · have hv : x.val ≠ 0 := by intro h;apply hx;apply UScalar.eq_of_val_eq;simpa using h
    simp [hx,hv]

theorem append_bit (p : RP) (n : Usize) (hn : n.val < 64) :
    app_bit_r p n = ok (appBitR (wordPublic p) n.val) := by
  have hv : (BuilderStdModels.shift64 p.next_pair_index n).val = p.next_pair_index.val >>> n.val := by
    rw [BuilderStdModels.shift64_spec]
    change (p.next_pair_index.bv.ushiftRight (n.val%64)).toNat = _
    rw [Nat.mod_eq_of_lt hn]
    rfl
  simp only [app_bit_r,lift,bind_tc_ok,nonzero,appBitR,wordPublic,UScalar.val_and,hv,UScalar.ofNatCore_val_eq]
  rfl

theorem append_sibling (p : RP) (n : Usize) (hn : n.val < 20) :
    app_sib_r p n = ok (appSibR (wordPublic p) n.val) := by
  rw [app_sib_r,append_bit p n (by omega)]
  simp only [bind_tc_ok]
  unfold appSibR
  split <;> exact index_ok_gen _ n (by simpa using hn)

theorem append (w : RW) (p : RP) (n : Usize) (hn : n.val ≤ 20) :
    app_cur_r w p n = appCurR (wordWitness w) (wordPublic p) n.val := by
  generalize he : n.val = k
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    rw [app_cur_r]
    by_cases hz : n.val = 0
    · have hn0 : n = 0#usize := by apply UScalar.eq_of_val_eq;simpa using hz
      rw [if_pos hn0,← he,hz]
      exact output_pair w p
    · have hn0 : n ≠ 0#usize := by intro h;apply hz;simpa [h] using congrArg UScalar.val h
      rw [if_neg hn0]
      simp only [lift,bind_tc_ok]
      have hv : (Usize.wrapping_sub n 1#usize).val = n.val-1 :=
        R0Z.WriterRefine.usub _ _ (by simp;omega)
      have hk : (Usize.wrapping_sub n 1#usize).val < k := by omega
      rw [ih _ hk _ (by omega) rfl]
      rw [append_sibling p _ (by rw [hv];omega)]
      simp only [bind_tc_ok]
      rw [append_bit p _ (by rw [hv];omega)]
      simp only [bind_tc_ok,ordered,node_digest]
      rw [hv]
      conv_rhs => rw [← he,show n.val = (n.val-1)+1 by omega,appCurR]

theorem append_ok (w : RW) (p : RP) (n : Usize) (hn : n.val ≤ 20) :
    app_cur_r w p n = ok (okOr (appCurR (wordWitness w) (wordPublic p) n.val) zero8) := by
  obtain ⟨c,hc⟩ := append_total (wordWitness w) (wordPublic p) n.val
  rw [append w p n hn,hc,okOr_ok]

#print axioms output_pair
#print axioms pair_total
#print axioms append_total
#print axioms nonzero
#print axioms append_bit
#print axioms append_sibling
#print axioms append
#print axioms append_ok
end R1Z.PV_Src_Forest_AppendArguments
