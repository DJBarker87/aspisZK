import S2K_DigestTotal

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1.S2K.AfterstateLoop
open AspisR1TerminalDecoder LoopStep
abbrev Rows := Array Digest 20#usize

def Inv (rows : Rows) (s : Iter × Array U8 688#usize) : Prop :=
  ∃ k : Usize, k.val ≤ 20 ∧ s.1 = Iterator.cursor rows k

theorem loop_total (rows : Rows) (count : Usize) (bound : count.val ≤ 20)
    (output : Array U8 688#usize) :
    WP.spec (pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
      (Iterator.cursor rows count) output) (fun _ => True) := by
  unfold pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
  refine loop.spec_decr_nat
    (fun s : Iter × Array U8 688#usize => 20-s.1.count.val)
    (Inv rows) (fun _ : Array U8 688#usize => True)
    (fun s : Iter × Array U8 688#usize => body s.1 s.2)
    (Iterator.cursor rows count,output) ?_ ⟨count,bound,rfl⟩
  rintro ⟨iter,out⟩ ⟨k,hk,same⟩
  change iter = Iterator.cursor rows k at same
  simp only [same]
  by_cases more : k.val < 20
  · obtain ⟨bytes,encoded⟩ := DigestTotal.total (rows.val[k.val]'(by have := rows.property; change rows.val.length = 20 at this; omega))
    rw [body_write _ _ out k _ bytes (Iterator.next_row rows k more) more encoded]
    change (Inv rows (_,_) ∧ (20-(Usize.ofNatCore (k.val+1) _).val) < 20-k.val)
    refine ⟨⟨Usize.ofNatCore (k.val+1) (by scalar_tac),?_,rfl⟩,?_⟩
    · change k.val+1 ≤ 20; omega
    · change 20-(k.val+1) < 20-k.val; omega
  · have eqk : k = 20#usize := by scalar_tac
    subst k
    rw [body_done _ _ out (Iterator.exhausted rows)]
    trivial

theorem total (rows : Rows) (output : Array U8 688#usize) :
    ∃ bytes, pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
      (Iterator.cursor rows 0#usize) output = ok bytes := by
  have h := loop_total rows 0#usize (by decide) output
  cases result : pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
      (Iterator.cursor rows 0#usize) output with
  | fail e => simp only [result,WP.spec,WP.theta] at h
  | div => simp only [result,WP.spec,WP.theta] at h
  | ok bytes => exact ⟨bytes,rfl⟩

#print axioms loop_total
#print axioms total
end AspisR1.S2K.AfterstateLoop
