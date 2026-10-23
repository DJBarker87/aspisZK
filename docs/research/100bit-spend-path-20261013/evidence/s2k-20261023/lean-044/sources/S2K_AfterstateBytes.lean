import S2K_DigestBytes

/-! Symbolic byte equality for the actual digest loop. Words stay arbitrary;
no concrete recurrence or output array is kernel-normalized. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1.S2K.AfterstateBytes
open AspisR1TerminalDecoder LoopStep
abbrev Rows := AfterstateLoop.Rows

def fold : List Digest → Nat → Array U8 6820#usize → Array U8 6820#usize
  | [], _, out => out
  | node::rest, k, out => fold rest (k+1) (out.setSlice! (48+32*k) (DigestBytes.bytes node).val)

def Inv (rows : Rows) (target : Array U8 6820#usize) (s : Iter × Array U8 6820#usize) : Prop :=
  ∃ k : Usize, k.val ≤ 20 ∧ s.1 = Iterator.cursor rows k ∧ fold (rows.val.drop k.val) k.val s.2 = target

theorem loop_exact (rows : Rows) (count : Usize) (bound : count.val ≤ 20)
    (output : Array U8 6820#usize) :
    pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop (Iterator.cursor rows count) output =
      ok (fold (rows.val.drop count.val) count.val output) := by
  let target := fold (rows.val.drop count.val) count.val output
  have h : WP.spec (pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop (Iterator.cursor rows count) output)
      (fun out => out = target) := by
    unfold pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
    refine loop.spec_decr_nat
      (fun s : Iter × Array U8 6820#usize => 20-s.1.count.val)
      (Inv rows target) (fun out : Array U8 6820#usize => out=target)
      (fun s : Iter × Array U8 6820#usize => body s.1 s.2)
      (Iterator.cursor rows count,output) ?_ ⟨count,bound,rfl,rfl⟩
    rintro ⟨iter,out⟩ ⟨k,hk,same,rest⟩
    change iter = Iterator.cursor rows k at same
    simp only [same]
    by_cases more : k.val < 20
    · have valid : k.val < rows.val.length := by rw [rows.property]; exact more
      have dropped := List.drop_eq_getElem_cons valid
      rw [body_write _ _ out k _ (DigestBytes.bytes (rows.val[k.val]'valid))
        (Iterator.next_row rows k more) more (DigestBytes.exact (rows.val[k.val]'valid))]
      change (Inv rows target (_,_) ∧ (20-(Usize.ofNatCore (k.val+1) _).val) < 20-k.val)
      refine ⟨⟨Usize.ofNatCore (k.val+1) (by scalar_tac),?_,rfl,?_⟩,?_⟩
      · change k.val+1 ≤ 20; omega
      · change fold (rows.val.drop (k.val+1)) (k.val+1) _ = target
        simpa only [dropped,fold] using rest
      · change 20-(k.val+1) < 20-k.val; omega
    · have eqk : k=20#usize := by scalar_tac
      subst k
      have stopped := body_done _ _ out (Iterator.exhausted rows)
      rw [stopped]
      change out=target
      have ending : rows.val.drop (20#usize).val = [] := List.drop_eq_nil_of_le (by
        change rows.val.length ≤ 20
        have := rows.property
        change rows.val.length=20 at this
        omega)
      simpa only [ending,fold] using rest
  cases run : pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop (Iterator.cursor rows count) output with
  | fail e => simp only [run,WP.spec,WP.theta] at h
  | div => simp only [run,WP.spec,WP.theta] at h
  | ok out =>
    simp only [run,WP.spec,WP.theta,WP.wp_return] at h
    change out=target at h
    rw [h]

#print axioms loop_exact
end AspisR1.S2K.AfterstateBytes
