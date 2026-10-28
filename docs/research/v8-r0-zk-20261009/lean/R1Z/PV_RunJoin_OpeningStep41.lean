import R1Z.PV_RunJoin_OpeningCell41
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningStep41
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_OpeningCell41
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact

theorem base_stop (ops : ExternalFuns) (row : Array W 29#usize)
    (out : alloc.vec.Vec U8) (i : Usize) (stop : 26≤i.val) :
    @prover.append_opening_base_row_loop.body _ (ProverRwP6BodyCandidate.selected ops) row out i=.ok (.done out) := by
  simp only [prover.append_opening_base_row_loop.body,show ¬i<26#usize from (by change ¬i.val<26;omega),↓reduceIte]

theorem base_step (ops : ExternalFuns) (p : Nat → W)
    (out : alloc.vec.Vec U8) (i : Usize) (bound : i.val<26)
    (room : out.length+4≤Usize.max) :
    ∃ next, @prover.append_opening_base_row_loop.body _ (ProverRwP6BodyCandidate.selected ops)
      (ProverCommitArray49.array 29#usize p) out i=
        .ok (.cont (next,Usize.wrapping_add i 1#usize)) ∧
      next.val=out.val ++ piece (p i.val) 4 := by
  obtain ⟨next,hn,hv⟩ := PV_RunJoin_OpeningCell41.append ops (p i.val) out
    4#usize (by decide) room
  refine ⟨next,?_,hv⟩
  unfold prover.append_opening_base_row_loop.body
  simp only [show i<26#usize from bound,↓reduceIte]
  rw [ProverCommitArray49.index 29#usize p i (by omega)]
  simp only [bind_tc_ok]
  change (do
    let next ← (do
      let bytes ← @aspis_core.field.wide_exact.WideExact.to_le_bytes _
        (ProverRwP6BodyCandidate.selected ops) (p i.val)
      let s ← core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice U8)) bytes { «end» :=4#usize }
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s)
    .ok (.cont (next,Usize.wrapping_add i 1#usize)))= _
  rw [hn]
  rfl
#print axioms base_stop
#print axioms base_step

theorem secure_stop (ops : ExternalFuns) (row : Array W 29#usize)
    (out : alloc.vec.Vec U8) (i : Usize) (stop : 28≤i.val) :
    @prover.append_opening_secure_row_loop.body _ (ProverRwP6BodyCandidate.selected ops) row out i=.ok (.done out) := by
  simp only [prover.append_opening_secure_row_loop.body,show ¬i<28#usize from (by change ¬i.val<28;omega),↓reduceIte]

theorem secure_step (ops : ExternalFuns) (p : Nat → W)
    (out : alloc.vec.Vec U8) (i : Usize) (bound : i.val<28)
    (room : out.length+16≤Usize.max) :
    ∃ next, @prover.append_opening_secure_row_loop.body _ (ProverRwP6BodyCandidate.selected ops)
      (ProverCommitArray49.array 29#usize p) out i=
        .ok (.cont (next,Usize.wrapping_add i 1#usize)) ∧
      next.val=out.val ++ piece (p i.val) 16 := by
  obtain ⟨next,hn,hv⟩ := PV_RunJoin_OpeningCell41.append ops (p i.val) out
    16#usize (by decide) room
  refine ⟨next,?_,hv⟩
  unfold prover.append_opening_secure_row_loop.body
  simp only [show i<28#usize from bound,↓reduceIte]
  rw [ProverCommitArray49.index 29#usize p i (by omega)]
  simp only [bind_tc_ok]
  change (do
    let next ← (do
      let bytes ← @aspis_core.field.wide_exact.WideExact.to_le_bytes _
        (ProverRwP6BodyCandidate.selected ops) (p i.val)
      let s ← core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice U8)) bytes { «end» :=16#usize }
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s)
    .ok (.cont (next,Usize.wrapping_add i 1#usize)))= _
  rw [hn]
  rfl
#print axioms secure_stop
#print axioms secure_step
end R1Z.PV_RunJoin_OpeningStep41
