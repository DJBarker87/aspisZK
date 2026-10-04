import AspisV8R19.R663CombineWrapperExecution
import AspisV8R19.R677C1ChunkCanonical
import AspisV8R19.R616MixedLimbExecution
import AspisV8R19.R635DecoderWholeCanonical
import AspisV8R19.R646CombineLoopExecution
import AspisR614SelectedCombineBeta.Funs
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R687CombineBetaComposition
open Aeneas Aeneas.Std Result ControlFlow
open AspisR614SelectedCombineBeta
open AspisV8R19.R646CombineLoopExecution AspisV8R19.R663CombineWrapperExecution
open AspisV8R19.R677C1ChunkCanonical
open scoped BigOperators
noncomputable section
private abbrev U4 := Fin 4
private abbrev P : Nat := 2147483647

def arrayAt {α : Type} {n : Usize} (a : Aeneas.Std.Array α n) (i : Fin n.val) : α :=
  a.val[i.val]'(by rw [a.property]; exact i.isLt)

theorem combine_beta_success_canonical_limbs
    (c1 c2 : Slice U8) (powers : query_arithmetic.BetaCoefficients)
    (a1 : Std.Array U32 104#usize) (a2 : Std.Array U32 48#usize)
    (h1 : query_arithmetic.r55_decode_into c1 (Array.repeat 104#usize 0#u32) =
      .ok (core.result.Result.Ok (), a1))
    (h2 : query_arithmetic.r55_decode_into c2 (Array.repeat 48#usize 0#u32) =
      .ok (core.result.Result.Ok (), a2))
    (hp1 : ∀ i : Fin 26, ∀ r : Fin 4, (arrayAt (arrayAt powers.c1_limbs i) r).val < P)
    (hp2 : ∀ i : Fin 12, ∀ r : Fin 4, (arrayAt (arrayAt powers.mixed i) r).val < P) :
    ∃ lane : U4 → U4 → U32,
      query_arithmetic.combine_beta c1 c2 powers = .ok (core.result.Result.Ok (laneArray lane)) ∧
      (∀ slot limb, (lane slot limb).val < P) := by
  have hc1 : ∀ i : Fin 104, a1.val[i.val].val < P := by
    intro i
    have h := AspisV8R19.R635DecoderWholeCanonical.decoder_accepted_canonical
      (show (104#usize : Usize).val ≤ 104 by decide) c1 (Array.repeat 104#usize 0#u32) a1 h1
    exact h a1.val[i.val] (List.getElem_mem _)
  have hc2 : ∀ i : Fin 48, a2.val[i.val].val < P := by
    intro i
    have h := AspisV8R19.R635DecoderWholeCanonical.decoder_accepted_canonical
      (show (48#usize : Usize).val ≤ 104 by decide) c2 (Array.repeat 48#usize 0#u32) a2 h2
    exact h a2.val[i.val] (List.getElem_mem _)
  have hleaf (slot limb : U4) : ∃ z : aspis_core.field.M31,
      query_arithmetic.r83_mixed_limb (UScalar.ofNatCore limb.val (by have h := Usize.cMax_bound; scalar_tac))
        (c1Chunk a1 slot) a2 (sourceIndex slot) powers = .ok z ∧ z.val < P := by
    have hslot : (sourceIndex slot).val < 4 := by
      unfold sourceIndex
      change slot.val < 4
      exact slot.isLt
    have hchunk : ∀ i : Fin 26, (arrayAt (c1Chunk a1 slot) i).val < P := by
      intro i
      change (c1Chunk a1 slot).val[i.val].val < P
      rw [c1Chunk_getElem]
      exact hc1 ⟨26*slot.val+i.val,by omega⟩
    have hz := AspisV8R19.R616MixedLimbExecution.r83_mixed_limb_full
      (UScalar.ofNatCore limb.val (by have h := Usize.cMax_bound; scalar_tac)) (sourceIndex slot)
      (c1Chunk a1 slot) a2 powers (by simpa only [UScalar.ofNatCore_val_eq] using limb.isLt) hslot hchunk hc2 hp1 hp2
    rcases hz with ⟨z,hz,hcan,_⟩
    exact ⟨z,hz,hcan⟩
  choose lane hlane hcan using hleaf
  refine ⟨lane, ?_, ?_⟩
  · apply combine_beta_wrapper_execution c1 c2 powers a1 a2 lane h1 h2
    intro slot limb
    simpa using hlane slot limb
  · intro slot limb
    exact hcan slot limb
#print axioms combine_beta_success_canonical_limbs
end
end AspisV8R19.R687CombineBetaComposition
