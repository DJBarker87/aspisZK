import AspisR1ProducerRelease47.EncoderGeneric54
import R1Z.ProverCommitEncoderCollect54
/-! The complete collector law for every native CodeField carrier. -/
set_option autoImplicit false
namespace R1Z.ProverCommitEncoderGenericCollect54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitEncoderCollect54
theorem collect {E : Type} (inst : scalar.CodeField E) (c : Slice E) (stride offset i left : Usize) (n : Nat)
    (hn : left.val=n) (hcounter : i.val+n<1025)
    (hstride : stride.val≤4) (hoff : offset.val<4)
    (hread : ∀ k, k<n → stride.val*(i.val+k)+offset.val<c.val.length)
    (out : alloc.vec.Vec E) (hcapacity : out.val.length+n≤1024) :
    ∃ result, generic54.collect inst c stride offset i left out=ok result ∧
      result.val=out.val ++ List.ofFn (fun k : Fin n => c.val[stride.val*(i.val+k.val)+offset.val]'(hread k.val k.isLt)) := by
  induction n generalizing i left out with
  | zero =>
    have hz : left=0#usize := by scalar_tac
    refine ⟨out,?_,?_⟩
    · rw [generic54.collect,hz];rfl
    · simp
  | succ n ih =>
    have hne : left≠0#usize := by scalar_tac
    have hinc : (Usize.wrapping_add i 1#usize).val=i.val+1 :=
      ProverCommitPairCounter47.next_val i (by omega)
    have hdec : (Usize.wrapping_sub left 1#usize).val=n := by
      rw [sub_one left (by omega)];omega
    let idx := Usize.wrapping_add (Usize.wrapping_mul stride i) offset
    have hidx : idx.val=stride.val*i.val+offset.val := by
      dsimp only [idx]
      rw [Usize.wrapping_add_val_eq,Usize.wrapping_mul_val_eq]
      have hb : stride.val*i.val≤4096 := Nat.mul_le_mul hstride (show i.val≤1024 by omega)
      have hs := usize_bound
      have hm : stride.val*i.val<UScalar.size .Usize := by omega
      rw [Nat.mod_eq_of_lt hm]
      have ha : stride.val*i.val+offset.val<UScalar.size .Usize := by omega
      exact Nat.mod_eq_of_lt ha
    have hr : idx.val<c.val.length := by simpa only [hidx,Nat.add_zero] using hread 0 (by omega)
    obtain ⟨v,hv,hval⟩ := wp_exists _ _ (Slice.index_usize_spec c idx hr)
    obtain ⟨p,hp,hpval⟩ := wp_exists _ _ (alloc.vec.Vec.push_spec out v (by scalar_tac))
    obtain ⟨result,hresult,hlist⟩ := ih (Usize.wrapping_add i 1#usize) _ hdec
      (by rw [hinc];omega) (by intro k hk;rw [hinc];simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hread (k+1) (by omega))
      p (by rw [hpval,List.length_append];simp only [List.length_singleton];omega)
    refine ⟨result,?_,?_⟩
    · rw [generic54.collect]
      simp only [hne,if_false,lift,bind_tc_ok]
      change (do
        let v ← Slice.index_usize c idx
        let p ← alloc.vec.Vec.push out v
        generic54.collect inst c stride offset (Usize.wrapping_add i 1#usize)
          (Usize.wrapping_sub left 1#usize) p)=_
      rw [hv];simp only [bind_tc_ok];rw [hp];simp only [bind_tc_ok];exact hresult
    · rw [hlist,hpval,hval,List.ofFn_succ,List.append_assoc]
      congr 1
      simp only [List.singleton_append,List.cons.injEq]
      constructor
      · simp [hidx]
      · congr 1
        funext k
        simp only [hinc,Fin.val_succ]
        simp only [Nat.add_assoc,Nat.add_comm 1 k.val]

#print axioms collect
end R1Z.ProverCommitEncoderGenericCollect54
