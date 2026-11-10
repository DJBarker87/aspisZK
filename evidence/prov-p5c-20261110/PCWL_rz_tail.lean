
end PRVFresh_ARM_w7
end AdapterRw

set_option maxHeartbeats 200000

namespace PRVEq.AdapterRwModel_w7
open AdapterRw

/-- one step of the Aeneas `loop` functional (as in PRVC_LoopBridge) -/
def bs {α β : Type _} (body : α → Result (ControlFlow α β)) (h : α → Result β) (x : α) : Result β :=
  match body x with
  | ok r => match r with
    | ControlFlow.cont x' => h x'
    | ControlFlow.done y => ok y
  | fail e => fail e
  | div => div

theorem loop_unfold {α β : Type _} (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = bs body (loop body) x := by
  rw [loop]; rfl
#print axioms loop_unfold

/-- the pure specification: Ok iff every byte is zero, otherwise AccountAlreadyInitialized -/
def zs : List Std.U8 → core.result.Result Unit solana_program_error.ProgramError
  | [] => core.result.Result.Ok ()
  | b :: t => if (b != 0#u8) = true then core.result.Result.Err solana_program_error.ProgramError.AccountAlreadyInitialized else zs t

namespace F
open PRVFresh_ARM_w7.r1_pool_adapter.owned

theorem body_nil (s : Slice Std.U8) (hs : s.val = []) :
    require_zero_loop.body s = ok (done (core.result.Result.Ok ())) := by
  simp [require_zero_loop.body, core.slice.Slice.is_empty, Slice.length, hs]

theorem idx0 (s : Slice Std.U8) (b : Std.U8) (t : List Std.U8) (hs : s.val = b :: t) :
    Slice.index_usize s 0#usize = ok b := by
  simp [Slice.index_usize, hs]

theorem body_nz (s : Slice Std.U8) (b : Std.U8) (t : List Std.U8) (hs : s.val = b :: t) (hb : ¬ b.val = 0) :
    require_zero_loop.body s = ok (done (core.result.Result.Err solana_program_error.ProgramError.AccountAlreadyInitialized)) := by
  simp [require_zero_loop.body, core.slice.Slice.is_empty, Slice.length, hs, idx0 s b t hs, hb]

theorem body_z (s : Slice Std.U8) (b : Std.U8) (t : List Std.U8) (hs : s.val = b :: t) (hb : b.val = 0) :
    ∃ s' : Slice Std.U8, s'.val = t ∧ require_zero_loop.body s = ok (cont s') := by
  refine ⟨s.drop 1#usize, ?_, ?_⟩
  · simp [Slice.drop, hs]
  · simp [require_zero_loop.body, core.slice.Slice.is_empty, Slice.length, hs, idx0 s b t hs, hb,
      core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice,
      core.slice.index.SliceIndexRangeFromUsizeSlice.index]

end F

theorem fresh_loop (l : List Std.U8) : ∀ s : Slice Std.U8, s.val = l →
    PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero_loop s = ok (zs l) := by
  induction l with
  | nil =>
    intro s hs
    unfold PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero_loop
    rw [loop_unfold]
    simp only [bs]
    rw [F.body_nil s hs]
    rfl
  | cons b t ih =>
    intro s hs
    unfold PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero_loop
    rw [loop_unfold]
    simp only [bs]
    by_cases hb0 : b.val = 0
    · obtain ⟨s', hv, hbz⟩ := F.body_z s b t hs hb0
      rw [hbz]
      have := ih s' hv
      simp [zs, hb0]
      exact this
    · rw [F.body_nz s b t hs hb0]
      simp [zs, hb0]
#print axioms fresh_loop


theorem usize_lt_iff (a b : Usize) : (a < b) ↔ a.val < b.val := by
  exact UScalar.lt_equiv a b

theorem wadd_val (i : Usize) (n : Nat) (hn : i.val < n) (hl : n ≤ Usize.max) : (i.wrapping_add 1#usize).val = i.val + 1 := by
  have h := UScalar.wrapping_add_val_eq i 1#usize
  have h1 : (1#usize).val = 1 := by simp
  rw [h1] at h
  show (UScalar.wrapping_add i 1#usize).val = i.val + 1
  rw [h]
  apply Nat.mod_eq_of_lt
  rw [UScalar.size_UScalarTyUsize, Usize.size_def]
  have h2 := Usize.max_def
  have h3 : 1 ≤ 2 ^ Usize.numBits := Nat.one_le_two_pow
  omega

theorem idx_at (s : Slice Std.U8) (i : Usize) (h : i.val < s.val.length) : Slice.index_usize s i = ok (s.val[i.val]'h) := by
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, h]

/-- pure specification of the gate loop result at index i -/
def gs : List Std.U8 → Option (core.result.Result Unit solana_program_error.ProgramError)
  | [] => none
  | b :: t => if (b != 0#u8) = true then some (core.result.Result.Err solana_program_error.ProgramError.AccountAlreadyInitialized) else gs t

theorem zs_gs (l : List Std.U8) : zs l = (match gs l with | none => core.result.Result.Ok () | some r => r) := by
  induction l with
  | nil => rfl
  | cons b t ih => by_cases hb : b.val = 0 <;> simp [zs, gs, hb, ih]

namespace G
open AdapterRw.r1_pool_adapter.owned

theorem lt_len (bytes : Slice Std.U8) (i : Usize) : (i < bytes.len) ↔ i.val < bytes.val.length := by
  rw [usize_lt_iff]; simp

theorem body_end (bytes : Slice Std.U8) (i : Usize) (h : bytes.val.length ≤ i.val) :
    require_zero_loop.body bytes i = ok (done none) := by
  have : ¬ (i < bytes.len) := by rw [lt_len]; omega
  simp [require_zero_loop.body, this]

theorem body_nz (bytes : Slice Std.U8) (i : Usize) (h : i.val < bytes.val.length) (hb : ¬ (bytes.val[i.val]'h).val = 0) :
    require_zero_loop.body bytes i = ok (done (some (core.result.Result.Err solana_program_error.ProgramError.AccountAlreadyInitialized))) := by
  have := (lt_len bytes i).2 h
  simp [require_zero_loop.body, this, idx_at bytes i h, hb]

theorem body_z (bytes : Slice Std.U8) (i : Usize) (h : i.val < bytes.val.length) (hb : (bytes.val[i.val]'h).val = 0) :
    require_zero_loop.body bytes i = ok (cont (i.wrapping_add 1#usize)) := by
  have := (lt_len bytes i).2 h
  simp [require_zero_loop.body, this, idx_at bytes i h, hb, lift]

end G

theorem gate_loop (bytes : Slice Std.U8) : ∀ (k : Nat) (i : Usize), bytes.val.length - i.val = k → i.val ≤ bytes.val.length →
    AdapterRw.r1_pool_adapter.owned.require_zero_loop bytes i = ok (gs (bytes.val.drop i.val)) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    unfold AdapterRw.r1_pool_adapter.owned.require_zero_loop
    rw [loop_unfold]
    simp only [bs]
    rw [G.body_end bytes i (by omega)]
    simp [gs, List.drop_eq_nil_of_le (show bytes.val.length ≤ i.val by omega)]
  | succ k ih =>
    intro i hk hi
    have hlt : i.val < bytes.val.length := by omega
    unfold AdapterRw.r1_pool_adapter.owned.require_zero_loop
    rw [loop_unfold]
    simp only [bs]
    have hd : bytes.val.drop i.val = bytes.val[i.val] :: bytes.val.drop (i.val + 1) := List.drop_eq_getElem_cons hlt
    by_cases hb : (bytes.val[i.val]'hlt).val = 0
    · rw [G.body_z bytes i hlt hb]
      have hv := wadd_val i bytes.val.length hlt bytes.property
      have := ih (i.wrapping_add 1#usize) (by omega) (by omega)
      rw [hd]
      simp [gs, hb]
      rw [← hv]
      exact this
    · rw [G.body_nz bytes i hlt hb, hd]
      simp [gs, hb]

theorem require_zero_eq :
    @PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero = @AdapterRw.r1_pool_adapter.owned.require_zero := by
  funext bytes
  have hf := fresh_loop bytes.val bytes rfl
  have hg := gate_loop bytes (bytes.val.length - (0#usize).val) 0#usize rfl (by simp)
  unfold PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero AdapterRw.r1_pool_adapter.owned.require_zero
  rw [hf, hg]
  simp [zs_gs]
  cases gs bytes.val <;> rfl
#print axioms require_zero_eq

end PRVEq.AdapterRwModel_w7
