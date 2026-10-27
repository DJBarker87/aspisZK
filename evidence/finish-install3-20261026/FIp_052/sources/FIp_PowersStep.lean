import FIp_PowersWrite
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_PowersStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open FIp_PowersState
theorem step {N : Usize} (x : NE) (hx : FIo_WideValues.Canon x)
    (s : State N) (inv : FIp_PowersState.Inv x s) (out : ControlFlow (State N) (Array NE N))
    (run : FIo_Native.weights.powers_loop.body x s.1 s.2.1 s.2.2=ok out) :
    match out with
    | .done a => FIp_PowersState.Post x a
    | .cont t => FIp_PowersState.Inv x t ∧ FIo_PowersCanonical.measure t<FIo_PowersCanonical.measure s := by
  rcases s with ⟨a,p,i⟩
  dsimp only [FIp_PowersState.Inv] at inv
  unfold FIo_Native.weights.powers_loop.body at run
  split at run
  · rename_i more
    obtain ⟨⟨old,back⟩,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    have hc := FIo_ArrayBack.canonical a i old back hb inv.1.1 p inv.1.2
    have hi : i.val<N.val := by scalar_tac
    have written := FIp_PowersWrite.written x p a i old back hb hi inv.2.2.1 inv.2.2.2
    split at run
    · have same : done (back p)=out := Result.ok.inj run
      subst out
      refine ⟨hc,?_⟩
      have size : i.val+1=N.val := by scalar_tac
      intro j hj
      exact written j (by omega)
    · obtain ⟨next,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      have same : cont (back p,next,Usize.wrapping_add i 1#usize)=out := Result.ok.inj run
      subst out
      have cn := (FIo_WideMulValues.mul p x next inv.1.2 hx hn).1
      have vn := (FIo_WideMulValues.mul p x next inv.1.2 hx hn).2
      have inc : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
        rw [Usize.wrapping_add_val_eq]
        change (i.val+1)%UScalar.size .Usize=i.val+1
        apply Nat.mod_eq_of_lt
        apply lt_of_le_of_lt (show i.val+1≤N.val from by scalar_tac)
        simpa only [UScalar.size,UScalar.val,UScalarTy.numBits] using N.bv.isLt
      refine ⟨⟨⟨hc,cn⟩,?_,?_,?_⟩,?_⟩
      · simp only [inc]; omega
      · simp only [inc]
        rw [vn,inv.2.2.1,pow_succ]
      · simpa only [inc] using written
      · simp only [FIo_PowersCanonical.measure,inc]
        omega
  · have same : done a=out := Result.ok.inj run
    subst out
    refine ⟨inv.1.1,?_⟩
    have hi : N.val≤i.val := by scalar_tac
    intro j hj
    exact inv.2.2.2 j (by omega)

#print axioms step
end AspisR1.FIp_PowersStep
end
