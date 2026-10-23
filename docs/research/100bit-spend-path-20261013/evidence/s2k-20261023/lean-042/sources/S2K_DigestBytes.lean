import S2K_AfterstateStatus

/-! Symbolic byte equality for the actual digest loop. Words stay arbitrary;
no concrete recurrence or output array is kernel-normalized. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1.S2K.DigestBytes
open AspisR1TerminalDecoder DigestTotal

def fold : List Word → Nat → Array U8 32#usize → Array U8 32#usize
  | [], _, out => out
  | word::rest, k, out => fold rest (k+1) (out.setSlice! (4*k) (core.num.U32.to_le_bytes word).val)

def Inv (rows : Digest) (target : Array U8 32#usize) (s : Iter × Array U8 32#usize) : Prop :=
  ∃ k : Usize, k.val ≤ 8 ∧ s.1 = cursor rows k ∧ fold (rows.val.drop k.val) k.val s.2 = target

theorem loop_exact (rows : Digest) (count : Usize) (bound : count.val ≤ 8)
    (output : Array U8 32#usize) :
    atomic_statement.encode_digest_canonical_loop (cursor rows count) output =
      ok (fold (rows.val.drop count.val) count.val output) := by
  let target := fold (rows.val.drop count.val) count.val output
  have h : WP.spec (atomic_statement.encode_digest_canonical_loop (cursor rows count) output)
      (fun out => out = target) := by
    unfold atomic_statement.encode_digest_canonical_loop
    refine loop.spec_decr_nat
      (fun s : Iter × Array U8 32#usize => 8-s.1.count.val)
      (Inv rows target) (fun out : Array U8 32#usize => out=target)
      (fun s : Iter × Array U8 32#usize => body s.1 s.2)
      (cursor rows count,output) ?_ ⟨count,bound,rfl,rfl⟩
    rintro ⟨iter,out⟩ ⟨k,hk,same,rest⟩
    change iter = cursor rows k at same
    simp only [same]
    by_cases more : k.val < 8
    · have valid : k.val < rows.val.length := by rw [rows.property]; exact more
      have dropped := List.drop_eq_getElem_cons valid
      rw [body_word rows k more out]
      change (Inv rows target (_,_) ∧ (8-(Usize.ofNatCore (k.val+1) _).val) < 8-k.val)
      refine ⟨⟨Usize.ofNatCore (k.val+1) (by scalar_tac),?_,rfl,?_⟩,?_⟩
      · change k.val+1 ≤ 8; omega
      · change fold (rows.val.drop (k.val+1)) (k.val+1) _ = target
        simpa only [dropped,fold] using rest
      · change 8-(k.val+1) < 8-k.val; omega
    · have eqk : k=8#usize := by scalar_tac
      subst k
      have stopped : body (cursor rows 8#usize) out = ok (done out) := by
        simp only [body, atomic_statement.encode_digest_canonical_loop.body,
          exhausted rows, bind_tc_ok]
        rfl
      rw [stopped]
      change out=target
      have ending : rows.val.drop (8#usize).val = [] := List.drop_eq_nil_of_le (by
        change 8 ≤ rows.val.length
        have := rows.property
        change rows.val.length=8 at this
        omega)
      simpa only [ending,fold] using rest
  cases run : atomic_statement.encode_digest_canonical_loop (cursor rows count) output with
  | fail e => simp only [run,WP.spec,WP.theta] at h
  | div => simp only [run,WP.spec,WP.theta] at h
  | ok out =>
    simp only [run,WP.spec,WP.theta,WP.wp_return] at h
    change out=target at h
    rw [h]

def bytes (rows : Digest) : Array U8 32#usize := fold rows.val 0 (Array.repeat 32#usize 0#u8)

theorem exact (rows : Digest) : atomic_statement.encode_digest_canonical rows = ok (bytes rows) := by
  have h := loop_exact rows 0#usize (by decide) (Array.repeat 32#usize 0#u8)
  change atomic_statement.encode_digest_canonical_loop (cursor rows 0#usize) (Array.repeat 32#usize 0#u8) = _
  have zero : (0#usize).val = 0 := rfl
  simpa only [zero,List.drop_zero,bytes] using h

#print axioms loop_exact
#print axioms exact
end AspisR1.S2K.DigestBytes
