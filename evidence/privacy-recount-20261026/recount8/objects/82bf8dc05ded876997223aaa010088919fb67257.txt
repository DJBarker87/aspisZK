import R1Z.ProverRwOuterWrite
set_option autoImplicit false
namespace R1Z.ProverRwOuterEncode
open Aeneas Aeneas.Std Result ProverRwOuterContext ProverRwOuterWrite

def factored (c : Context) : Result (Array U8 81#usize) := do
  let a ← Array.update (Array.repeat 81#usize 0#u8) 0#usize 1#u8
  let a ← write a 1#usize 33#usize c.statement_digest
  let a ← write a 33#usize 65#usize c.mask_nonce
  let a ← write a 65#usize 73#usize (core.num.U64.to_le_bytes c.mask_layout_fingerprint)
  write a 73#usize 81#usize (core.num.U64.to_le_bytes c.layout_factor_fingerprint)

theorem encode_factor (c : Context) : encode c = factored c := by
  unfold encode factored write
  simp only [lift,bind_tc_ok,bind_assoc_eq,Aeneas.Std.uncurry]
  rfl

def initial : Array U8 81#usize := (Array.repeat 81#usize 0#u8).set 0#usize 1#u8
def value (c : Context) : Array U8 81#usize :=
  put (put (put (put initial 1#usize c.statement_digest) 33#usize c.mask_nonce)
    65#usize (core.num.U64.to_le_bytes c.mask_layout_fingerprint))
    73#usize (core.num.U64.to_le_bytes c.layout_factor_fingerprint)

/-- All four native-source ranges and copy lengths are discharged; the
encoder cannot fail on any context. No successful-encoding premise remains. -/
theorem encode_total (c : Context) : encode c = .ok (value c) := by
  have start : Array.update (Array.repeat 81#usize 0#u8) 0#usize 1#u8 = .ok initial := by
    obtain ⟨a,ha,hv⟩ := WP.spec_imp_exists (Array.update_spec
      (Array.repeat 81#usize 0#u8) 0#usize 1#u8 (by decide))
    simpa only [hv,initial] using ha
  rw [encode_factor]
  unfold factored
  rw [start]
  simp only [bind_tc_ok]
  rw [write_exact _ 1#usize 33#usize _ (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [write_exact _ 33#usize 65#usize _ (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [write_exact _ 65#usize 73#usize _ (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  exact write_exact _ 73#usize 81#usize _ (by decide) (by decide) (by decide)

#print axioms encode_factor
#print axioms encode_total
end R1Z.ProverRwOuterEncode
