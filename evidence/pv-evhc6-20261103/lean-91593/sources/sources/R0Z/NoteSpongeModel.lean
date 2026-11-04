import R0Z.SpongeModel

/-! The extracted sponge writer on the note input (owner ‖ value ‖ asset ‖ salt,
note_input pair_trace.rs:227-234, domain 0x41530003, 18 words) produces
exactly the model's note blocks noteB0/noteB1/noteB2 (blocks 1..3, 27..29,
30..32 of buildModel), relative to RoundsOk for each permutation. -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result
open R0Z.BuilderModel

variable {K : Type} [Field K]

/-- The note sponge's model blocks. -/
def noteBlocks (o : R0P.Digest K) (v a : K) (s : R0P.Digest K) : Nat → BlockIn K :=
  fun q => if q = 0 then noteB0 o else if q = 1 then noteB1 o v a s else noteB2 o v a s

/-- The 18 note words lift to (owner, value, asset, salt). -/
structure NoteInputLift (input : Array U32 24#usize) (o : R0P.Digest K) (v a : K) (s : R0P.Digest K) : Prop where
  owner : ∀ i : Fin 8, liftU (K := K) (input.val[i.val]!) = o i
  value : liftU (K := K) (input.val[8]!) = v
  asset : liftU (K := K) (input.val[9]!) = a
  salt : ∀ i : Fin 8, liftU (K := K) (input.val[10 + i.val]!) = s i

theorem note_sponge_model (domain : U32) (hd : domain.val = 0x41530003) (input : Array U32 24#usize)
    (len : Usize) (hl : len.val = 18) (rounds : Array (Array (Array U32 16#usize) 11#usize) 3#usize)
    (o : R0P.Digest K) (v a : K) (s : R0P.Digest K) (hin : NoteInputLift input o v a s)
    (hr : ∀ q, q < 3 → RoundsOk (rounds.val[q]!) (noteBlocks o v a s q)) :
    ∃ out, R0BlockCopies.write_sponge domain input len rounds = ok out ∧
      ∀ q, q < 3 → ∀ (l c : Fin 16),
        liftU (K := K) (out.val[q * 256 + (l.val * 16 + c.val)]!) = blockCell (noteBlocks o v a s q) l.val c := by
  have hperm : (len.val + 7) / 8 = 3 := by rw [hl]
  have hS : SpongeLifts input len.val rounds (noteBlocks o v a s) := by
    refine ⟨fun q hq i => ?_, fun q hq => ?_, fun q hq => hr q (by omega)⟩
    · rw [hperm] at hq
      have hi := i.isLt
      rw [hl]
      have c0 : clenOf 18 0 = 8 := by decide
      have c1 : clenOf 18 1 = 8 := by decide
      have c2 : clenOf 18 2 = 2 := by decide
      interval_cases q
      · show lo8 o i = _
        unfold lo8
        rw [c0, show 8 * 0 + i.val = i.val by omega]
        by_cases h8 : i.val < 8
        · rw [dif_pos h8, if_pos ⟨h8, h8⟩]; exact (hin.owner ⟨i.val, h8⟩).symm
        · rw [dif_neg h8, if_neg (fun h => h8 h.1)]
      · show noteC2 v a s i = _
        unfold noteC2
        rw [c1]
        by_cases e0 : i.val = 0
        · rw [if_pos e0, if_pos ⟨by omega, by omega⟩, e0]; exact hin.value.symm
        rw [if_neg e0]
        by_cases e1 : i.val = 1
        · rw [if_pos e1, if_pos ⟨by omega, by omega⟩, e1]; exact hin.asset.symm
        rw [if_neg e1]
        by_cases h8 : i.val < 8
        · rw [dif_pos h8, if_pos ⟨h8, by omega⟩, show 8 * 1 + i.val = 10 + (i.val - 2) by omega]
          exact (hin.salt ⟨i.val - 2, by omega⟩).symm
        · rw [dif_neg h8, if_neg (fun h => h8 h.1)]
      · show noteC3 s i = _
        unfold noteC3
        rw [c2]
        by_cases e0 : i.val = 0
        · rw [if_pos e0, if_pos ⟨by omega, by omega⟩, e0]; exact (hin.salt 6).symm
        rw [if_neg e0]
        by_cases e1 : i.val = 1
        · rw [if_pos e1, if_pos ⟨by omega, by omega⟩, e1]; exact (hin.salt 7).symm
        rw [if_neg e1, if_neg (by omega)]
    · rw [hperm] at hq
      have hq2 : q < 2 := by omega
      interval_cases q <;> rfl
  obtain ⟨out, ho, hcells, _⟩ := sponge_model domain input len (by omega) rounds (noteBlocks o v a s) hS
    (fun i => by
      show spongeInit 0x4153_0003 18 i = _
      unfold spongeInit liftU
      rw [hd, hl]
      by_cases e8 : i.val = 8
      · rw [if_pos e8, if_pos e8]; norm_num
      · rw [if_neg e8, if_neg e8]
        by_cases e9 : i.val = 9
        · rw [if_pos e9, if_pos e9]; norm_num
        · rw [if_neg e9, if_neg e9])
  exact ⟨out, ho, fun q hq => hcells q (by omega)⟩

#print axioms note_sponge_model
end R0Z.WriterRefine
