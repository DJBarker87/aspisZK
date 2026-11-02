import R1Z.PV_RunJoin_MultilinearData69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MultilinearSparse69
open Aeneas Aeneas.Std Result PV_B3_Copy_222 PV_RunJoin_MultilinearField69

theorem complete (point : Array Q 10#usize) :
    ∃ out,host_multilinear.sparse_eq_weights point=ok out ∧
      out.len.val≤1024 ∧ PV_RunJoin_MultilinearData69.Valid out.data := by
  obtain ⟨pref,hp,hbound⟩ := PV_RunJoin_MultilinearPrefix69.complete point 10 10#usize rfl (by omega)
  let trailing := Usize.wrapping_sub 10#usize pref
  have ht : trailing.val=10-pref.val := by
    dsimp only [trailing]
    rw [Usize.wrapping_sub_val_eq]
    have large : 32≤UScalar.size .Usize := by
      rw [UScalar.size_def]
      exact le_trans (by decide : 32≤2^32) (Nat.pow_le_pow_right (by decide) System.Platform.le_numBits)
    change (10+(UScalar.size .Usize-pref.val))%UScalar.size .Usize=10-pref.val
    rw [show 10+(UScalar.size .Usize-pref.val)=(10-pref.val)+UScalar.size .Usize by omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  have sum : pref.val+trailing.val=10 := by omega
  obtain ⟨suffix,hs,hsmall⟩ := PV_RunJoin_MultilinearSuffix69.complete point pref.val (10-pref.val)
    pref 0#usize (by omega) (by omega) (by simp)
  have hs' : suffix.val<2^trailing.val := by simpa only [ht] using hsmall
  let bound := Usize.wrapping_shl 1#usize (UScalar.cast .U32 pref)
  have cast : (UScalar.cast .U32 pref).val=pref.val := by scalar_tac
  have powbound : 2^pref.val≤1024 := Nat.pow_le_pow_right (by decide) hbound
  have big : 1024<UScalar.size .Usize := by
    have h := System.Platform.le_numBits
    rw [UScalar.size_def]
    exact lt_of_lt_of_le (by decide : 1024<2^32) (Nat.pow_le_pow_right (by decide) h)
  have hb : bound.val=2^pref.val := by
    dsimp only [bound]
    rw [PV_RunJoin_MultilinearBits69.shift_val _ _ (by rw [cast];omega),cast]
    change (1*2^pref.val)%UScalar.size .Usize=2^pref.val
    rw [Nat.one_mul,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨out,ho,valid⟩ := PV_RunJoin_MultilinearData69.complete point pref trailing suffix bound
    hbound (by rw [hb];exact powbound)
    (fun i hi => PV_RunJoin_MultilinearRows69.complete i suffix trailing pref.val (by rwa [hb] at hi) sum hs')
    bound.val 0#usize (Array.repeat 1024#usize (0#usize,aspis_core.field.QM31.ZERO))
    (by simp) (by intro pair member;simp only [Array.repeat,List.mem_replicate] at member;rcases member with ⟨_,rfl⟩;decide)
  dsimp only [trailing,bound] at ho
  exact ⟨⟨out,bound⟩,by simp only [host_multilinear.sparse_eq_weights,hp,hs,ho,lift,bind_tc_ok],
    by rw [hb];exact powbound,valid⟩

#print axioms complete
end R1Z.PV_RunJoin_MultilinearSparse69
