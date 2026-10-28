import S2W_D189Wrappers
import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_ZeroLoop
open Aeneas Aeneas.Std Result ControlFlow
open _root_.AdapterRw

theorem index (bytes : Slice U8) (i : Usize) (inside : i.val<bytes.val.length)
    (byte : U8) (selected : bytes.val[i.val]?=some byte) :
    Slice.index_usize bytes i=ok byte := by
  have spec : Slice.index_usize bytes i ⦃ out => out=byte ⦄ := by
    step*
    simp_all
  obtain ⟨out,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

/-- Symbolic induction on the emitted model's remaining suffix, never kernel
reduction of the1768-cell checkpoint. Native iteration association is separate. -/
theorem certificate (bytes : Slice U8) (bound : bytes.val.length≤4096)
    (n : Nat) (i : Usize) (remaining : i.val+n=bytes.val.length)
    (out : Option (core.result.Result Unit solana_program_error.ProgramError))
    (call : r1_pool_adapter.owned.require_zero_loop bytes i=ok out) :
    (out=none ∧ ∀ j, i.val≤j → j<bytes.val.length → bytes.val[j]?=some 0#u8) ∨
      out=some (.Err solana_program_error.ProgramError.AccountAlreadyInitialized) := by
  induction n generalizing i out with
  | zero =>
    have outside : ¬ i<Slice.len bytes := by change ¬ i.val<bytes.val.length;omega
    unfold r1_pool_adapter.owned.require_zero_loop at call
    rw [Aeneas.Std.loop.eq_def] at call
    simp only [r1_pool_adapter.owned.require_zero_loop.body,if_neg outside,bind_tc_ok] at call
    have same : out=none := (Result.ok.inj call).symm
    exact Or.inl ⟨same,by intro j lo hi;omega⟩
  | succ n ih =>
    have inside : i.val<bytes.val.length := by omega
    let byte := bytes.val[i.val]'inside
    have read : Slice.index_usize bytes i=ok byte :=
      index bytes i inside byte (List.getElem?_eq_getElem inside)
    have within : i<Slice.len bytes := inside
    by_cases zeroByte : byte=0#u8
    · have inc : (Usize.wrapping_add i 1#usize).val=i.val+1 :=
        Port3_Wrapping.wrap_add_value i 1#usize (by change i.val+1≤4096;omega)
      have next : r1_pool_adapter.owned.require_zero_loop bytes (Usize.wrapping_add i 1#usize)=ok out := by
        unfold r1_pool_adapter.owned.require_zero_loop at call ⊢
        rw [Aeneas.Std.loop.eq_def] at call
        simpa only [r1_pool_adapter.owned.require_zero_loop.body,if_pos within,read,
          zeroByte,bne_self_eq_false,Bool.false_eq_true,if_false,lift,bind_tc_ok] using call
      rcases ih (Usize.wrapping_add i 1#usize) (by rw [inc];omega) out next with ⟨same,tail⟩|error
      · refine Or.inl ⟨same,?_⟩
        intro j lo hi
        by_cases sameIndex : j=i.val
        · subst j
          rw [List.getElem?_eq_getElem inside]
          exact congrArg some zeroByte
        · exact tail j (by rw [inc];omega) hi
      · exact Or.inr error
    · have nonzero : (byte!=0#u8)=true := by simpa only [bne_iff_ne] using zeroByte
      unfold r1_pool_adapter.owned.require_zero_loop at call
      rw [Aeneas.Std.loop.eq_def] at call
      simp only [r1_pool_adapter.owned.require_zero_loop.body,if_pos within,read,bind_tc_ok,
        nonzero,if_true] at call
      exact Or.inr (Result.ok.inj call).symm

/-- Successful model admission determines every initial checkpoint byte. -/
theorem accepted (bytes : Slice U8) (bound : bytes.val.length≤4096)
    (call : r1_pool_adapter.owned.require_zero bytes=ok (.Ok ())) :
    ∀ j, j<bytes.val.length → bytes.val[j]?=some 0#u8 := by
  unfold r1_pool_adapter.owned.require_zero at call
  obtain ⟨out,loopCall,rest⟩ := AspisR1.AdapterRw.Cuts.bind_success _ _ _ call
  have cert := certificate bytes bound bytes.val.length 0#usize
    (by change 0+bytes.val.length=bytes.val.length;omega) out loopCall
  rcases cert with ⟨same,zero⟩|error
  · intro j hi
    exact zero j (by change 0≤j;omega) hi
  · subst out
    cases rest

#print axioms index
#print axioms certificate
#print axioms accepted
end AspisR1.NCL_ZeroLoop
end
