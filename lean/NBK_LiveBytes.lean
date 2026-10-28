import NBK_LiveStep
import S2K_DigestBytes

/-! Symbolic byte equality for the actual frontier loop. Rows stay arbitrary;
no concrete recurrence or output array is kernel-normalized. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace NBK_LiveBytes
open AspisR1TerminalDecoder
open AspisR1.S2K
open AspisR1.S2K.LoopStep (Digest Iter next)
open NBK_LiveStep
abbrev Rows := AfterstateLoop.Rows

def fold : List Digest → Nat → Slice U8 → Slice U8
  | [], _, out => out
  | node::rest, k, out => fold rest (k+1) (out.setSlice! (160+32*k) (DigestBytes.bytes node).val)

def Inv (rows : Rows) (target : Slice U8) (s : Iter × Slice U8) : Prop :=
  ∃ k : Usize, k.val ≤ 20 ∧ s.1 = Iterator.cursor rows k ∧ s.2.length = 800 ∧ fold (rows.val.drop k.val) k.val s.2 = target

theorem loop_exact (rows : Rows) (count : Usize) (bound : count.val ≤ 20)
    (output : Slice U8) (size : output.length = 800) :
    pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop (Iterator.cursor rows count) output =
      ok (fold (rows.val.drop count.val) count.val output) := by
  let target := fold (rows.val.drop count.val) count.val output
  have h : WP.spec (pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop (Iterator.cursor rows count) output)
      (fun out => out = target) := by
    unfold pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop
    refine loop.spec_decr_nat
      (fun s : Iter × Slice U8 => 20-s.1.count.val)
      (Inv rows target) (fun out : Slice U8 => out=target)
      (fun s : Iter × Slice U8 => body s.1 s.2)
      (Iterator.cursor rows count,output) ?_ ⟨count,bound,rfl,size,rfl⟩
    rintro ⟨iter,out⟩ ⟨k,hk,same,sz,rest⟩
    change iter = Iterator.cursor rows k at same
    simp only [same]
    by_cases more : k.val < 20
    · have valid : k.val < rows.val.length := by rw [rows.property]; exact more
      have dropped := List.drop_eq_getElem_cons valid
      rw [body_write _ _ out k _ (DigestBytes.bytes (rows.val[k.val]'valid))
        (Iterator.next_row rows k more) more sz (DigestBytes.exact (rows.val[k.val]'valid))]
      change (Inv rows target (_,_) ∧ (20-(Usize.ofNatCore (k.val+1) _).val) < 20-k.val)
      refine ⟨⟨Usize.ofNatCore (k.val+1) (by scalar_tac),?_,rfl,?_,?_⟩,?_⟩
      · change k.val+1 ≤ 20; omega
      · simpa only [Slice.length,Slice.setSlice!,List.length_setSlice!] using sz
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
  cases run : pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop (Iterator.cursor rows count) output with
  | fail e => simp only [run,WP.spec,WP.theta] at h
  | div => simp only [run,WP.spec,WP.theta] at h
  | ok out =>
    simp only [run,WP.spec,WP.theta,WP.wp_return] at h
    change out=target at h
    rw [h]

#print axioms loop_exact
end NBK_LiveBytes
