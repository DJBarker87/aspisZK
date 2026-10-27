import R0Z.SpongeRefine

/-! The extracted sponge writer equals the model's sponge blocks
(DESIGN-BUILDER-MODEL §10), relative to the Poseidon plug-in RoundsOk. -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result

theorem usub (x y : Usize) (h : y.val ≤ x.val) : (Usize.wrapping_sub x y).val = x.val - y.val := by
  rw [Usize.wrapping_sub_val_eq]
  have hx := x.hSize
  have hs := usize_size_ge
  rw [show x.val + (UScalar.size .Usize - y.val) = (x.val - y.val) + UScalar.size .Usize by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

variable {K : Type} [Field K]

/-- The number of words the sponge absorbs in permutation q. -/
def clenOf (len q : Nat) : Nat := if len - 8 * q < 8 then len - 8 * q else 8

/-- The sponge's model premises: chunk absorptions, chaining, and rounds. -/
structure SpongeLifts (input : Array U32 24#usize) (len : Nat)
    (rounds : Array (Array (Array U32 16#usize) 11#usize) 3#usize)
    (B : Nat → R0Z.BuilderModel.BlockIn K) : Prop where
  absorb : ∀ q, q < (len + 7) / 8 → ∀ i : Fin 16, (B q).absorb i =
    (if i.val < 8 ∧ i.val < clenOf len q then liftU (K := K) (input.val[8 * q + i.val]!) else 0)
  chain : ∀ q, q + 1 < (len + 7) / 8 → (B (q + 1)).pre = R0Z.BuilderModel.blockOut (B q)
  rounds : ∀ q, q < (len + 7) / 8 → RoundsOk (rounds.val[q]!) (B q)

theorem sponge_loop_model (input : Array U32 24#usize) (len : Usize) (hlen : 1 ≤ len.val ∧ len.val ≤ 24)
    (rounds : Array (Array (Array U32 16#usize) 11#usize) 3#usize) (perms : Usize)
    (hperms : perms.val = (len.val + 7) / 8) (B : Nat → R0Z.BuilderModel.BlockIn K)
    (hS : SpongeLifts input len.val rounds B) :
    ∀ (n : Nat) (p : Usize) (out : Array U32 768#usize) (state : Array U32 16#usize),
      p.val + n = perms.val →
      (p.val < perms.val → ∀ i : Fin 16, liftU (K := K) (state.val[i.val]!) = (B p.val).pre i) →
      ∃ out', R0BlockCopies.write_sponge_loop input len rounds out state perms p = ok out' ∧
        (∀ q, p.val ≤ q → q < perms.val → ∀ (l c : Fin 16),
          liftU (K := K) (out'.val[q * 256 + (l.val * 16 + c.val)]!) = R0Z.BuilderModel.blockCell (B q) l.val c) ∧
        (∀ k, ¬ (p.val * 256 ≤ k ∧ k < perms.val * 256) → out'.val[k]! = out.val[k]!)
  | 0, p, out, state, h, _ => by
      refine ⟨out, ?_, fun q h1 h2 => by omega, fun k _ => rfl⟩
      rw [R0BlockCopies.write_sponge_loop, if_neg (by rw [UScalar.lt_equiv]; omega)]
  | n + 1, p, out, state, h, hst => by
      have hpp : p.val < perms.val := by omega
      have hp3 : p.val < 3 := by omega
      have hlt : p < perms := by rw [UScalar.lt_equiv]; exact hpp
      have h8p : (Usize.wrapping_mul 8#usize p).val = 8 * p.val := by rw [umul _ _ (by simp; omega)]; simp
      have h8lt : 8 * p.val < len.val := by omega
      have hsub : (Usize.wrapping_sub len (Usize.wrapping_mul 8#usize p)).val = len.val - 8 * p.val := by
        rw [usub _ _ (by rw [h8p]; omega), h8p]
      have hp1 : (Usize.wrapping_add p 1#usize).val = p.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨chunk, hch, hchs⟩ := sponge_chunk_spec input p hp3
      -- the clen value and the rest of the step, for either branch
      have step : ∀ clen : Usize, clen.val = clenOf len.val p.val →
          ∃ out', (do
            let a ← Array.index_usize rounds p
            let block ← R0BlockCopies.write_sponge_block state chunk clen a
            let out1 ← R0BlockCopies.place_block out p block
            let state1 ← Array.index_usize a 10#usize
            let p1 ← lift (Usize.wrapping_add p 1#usize)
            R0BlockCopies.write_sponge_loop input len rounds out1 state1 perms p1) = ok out' ∧
          (∀ q, p.val ≤ q → q < perms.val → ∀ (l c : Fin 16),
            liftU (K := K) (out'.val[q * 256 + (l.val * 16 + c.val)]!) = R0Z.BuilderModel.blockCell (B q) l.val c) ∧
          (∀ k, ¬ (p.val * 256 ≤ k ∧ k < perms.val * 256) → out'.val[k]! = out.val[k]!) := by
        intro clen hclen
        obtain ⟨ab, hab, habs⟩ := sponge_absorb_spec chunk clen
        have he : EndsLift state ab (B p.val) := by
          refine ⟨hst hpp, fun i => ?_⟩
          rw [hS.absorb p.val (by omega) i, habs, hclen]
          by_cases c : i.val < 8 ∧ i.val < clenOf len.val p.val
          · rw [if_pos c, if_pos c, hchs i.val c.1]
          · rw [if_neg c, if_neg c]; unfold liftU; simp
        have hrp : p.val < (3#usize).val := by simp; omega
        obtain ⟨blk, hblk, hbs⟩ := block_model state ab (rounds.val[p.val]!) (B p.val) he
          (hS.rounds p.val (by omega))
        obtain ⟨o1, ho1, ho1s⟩ := place_loop_spec p hp3 blk 256 0#usize out (by simp)
        have h10 : (10#usize : Usize).val < (11#usize).val := by simp
        have hst' : p.val + 1 < perms.val → ∀ i : Fin 16,
            liftU (K := K) (((rounds.val[p.val]!).val[(10#usize : Usize).val]!).val[i.val]!) =
              (B (p.val + 1)).pre i := by
          intro hq i
          rw [hS.chain p.val (by omega), show (10#usize : Usize).val = 10 by simp]
          exact hS.rounds p.val (by omega) 10 i (by norm_num)
        obtain ⟨out', ho', hcells, hrest⟩ := sponge_loop_model input len hlen rounds perms hperms B hS n
          (Usize.wrapping_add p 1#usize) o1 ((rounds.val[p.val]!).val[(10#usize : Usize).val]!)
          (by rw [hp1]; omega) (by rw [hp1]; exact hst')
        refine ⟨out', ?_, fun q h1 h2 l c => ?_, fun k hk => ?_⟩
        · rw [index_ok_gen rounds p hrp]
          simp only [bind_tc_ok]
          rw [R0BlockCopies.write_sponge_block, hab]
          simp only [bind_tc_ok]
          rw [hblk]
          simp only [bind_tc_ok]
          rw [R0BlockCopies.place_block, ho1]
          simp only [bind_tc_ok]
          rw [index_ok_gen (rounds.val[p.val]!) 10#usize h10]
          simp only [bind_tc_ok, lift]
          exact ho'
        · by_cases e : q = p.val
          · have z0 : (0#usize : Usize).val = 0 := by simp
            rw [hrest _ (by rw [hp1]; omega), ho1s, if_pos (show p.val * 256 + (0#usize : Usize).val ≤
              q * 256 + (l.val * 16 + c.val) ∧ q * 256 + (l.val * 16 + c.val) < p.val * 256 + 256 by
                rw [z0]; omega), e]
            rw [show p.val * 256 + (l.val * 16 + c.val) - p.val * 256 = l.val * 16 + c.val by omega]
            exact hbs l c
          · exact hcells q (by rw [hp1]; omega) h2 l c
        · have z0 : (0#usize : Usize).val = 0 := by simp
          have hk1 : ¬ ((p.val + 1) * 256 ≤ k ∧ k < perms.val * 256) := fun h' => hk ⟨by omega, h'.2⟩
          have hk2 : ¬ (p.val * 256 + 0 ≤ k ∧ k < p.val * 256 + 256) := fun h' => hk ⟨by omega, by omega⟩
          rw [hrest k (by rw [hp1]; exact hk1), ho1s, z0, if_neg hk2]
      rw [R0BlockCopies.write_sponge_loop, if_pos hlt, hch]
      simp only [bind_tc_ok, lift]
      by_cases c8 : Usize.wrapping_sub len (Usize.wrapping_mul 8#usize p) < 8#usize
      · rw [if_pos c8]
        have c8' : len.val - 8 * p.val < 8 := by rw [UScalar.lt_equiv, hsub] at c8; simpa using c8
        exact step _ (by rw [hsub]; unfold clenOf; rw [if_pos c8'])
      · rw [if_neg c8]
        have c8' : ¬ len.val - 8 * p.val < 8 := by rw [UScalar.lt_equiv, hsub] at c8; simpa using c8
        exact step _ (by simp only [clenOf, if_neg c8']; simp)

theorem rep768 (k : Nat) : (((Array.repeat 768#usize 0#u32 : Array U32 768#usize).val[k]! : U32)) = 0#u32 := by
  rw [Array.repeat_val]
  by_cases hk : k < (768#usize : Usize).val
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_pos hk]; rfl
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_neg hk]; rfl

/-- The extracted write_sponge equals the model's sponge blocks, every cell,
given the initial pre-state, the chunk absorptions, the chaining and RoundsOk;
blocks beyond ceil(len/8) are zero. -/
theorem sponge_model (domain : U32) (input : Array U32 24#usize) (len : Usize)
    (hlen : 1 ≤ len.val ∧ len.val ≤ 24) (rounds : Array (Array (Array U32 16#usize) 11#usize) 3#usize)
    (B : Nat → R0Z.BuilderModel.BlockIn K) (hS : SpongeLifts input len.val rounds B)
    (h0 : ∀ i : Fin 16, (B 0).pre i =
      if i.val = 8 then liftU (K := K) domain else if i.val = 9 then (len.val : K) else 0) :
    ∃ out, R0BlockCopies.write_sponge domain input len rounds = ok out ∧
      (∀ q, q < (len.val + 7) / 8 → ∀ (l c : Fin 16),
        liftU (K := K) (out.val[q * 256 + (l.val * 16 + c.val)]!) = R0Z.BuilderModel.blockCell (B q) l.val c) ∧
      (∀ k, (len.val + 7) / 8 * 256 ≤ k → out.val[k]! = 0#u32) := by
  have hcast : (UScalar.cast .U32 len).val = len.val := by
    rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by simp only [show UScalarTy.U32.numBits = 32 from rfl]; omega)
  obtain ⟨st, hst, hsts⟩ := sponge_init_spec domain (UScalar.cast .U32 len)
  have h7 : (Usize.wrapping_add len 7#usize).val = len.val + 7 := by rw [uadd _ _ (by scalar_tac)]; simp
  obtain ⟨perms, hp, hpv⟩ := UScalar.div_spec (Usize.wrapping_add len 7#usize) (y := 8#usize) (by simp)
  have hpv' : perms.val = (len.val + 7) / 8 := by rw [hpv, h7]; simp
  obtain ⟨out, ho, hcells, hrest⟩ := sponge_loop_model input len hlen rounds perms hpv' B hS ((len.val + 7) / 8)
    0#usize (Array.repeat 768#usize 0#u32) st (by simp; omega) (fun _ i => by
      rw [show (0#usize : Usize).val = 0 by simp, h0 i, hsts]
      unfold liftU
      by_cases e8 : i.val = 8
      · rw [if_pos e8, if_pos e8]
      · rw [if_neg e8, if_neg e8]
        by_cases e9 : i.val = 9
        · rw [if_pos e9, if_pos e9, hcast]
        · rw [if_neg e9, if_neg e9]; simp)
  refine ⟨out, ?_, fun q hq l c => hcells q (by simp) (by rw [hpv']; exact hq) l c, fun k hk => ?_⟩
  · rw [R0BlockCopies.write_sponge]
    simp only [lift, bind_tc_ok]
    rw [hst]
    simp only [bind_tc_ok]
    rw [show (Usize.wrapping_add len 7#usize) / 8#usize = ok perms from hp]
    simp only [bind_tc_ok]
    exact ho
  · rw [hrest k (by rw [hpv']; simp; omega), rep768]

#print axioms usub
#print axioms sponge_loop_model
#print axioms sponge_model
end R0Z.WriterRefine
