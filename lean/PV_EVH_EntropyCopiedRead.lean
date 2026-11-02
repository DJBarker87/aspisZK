import PV_EVH_StackByteCodec
import PV_EVH_EntropyHalves
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyCopiedRead
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_StackZero (State)

/-- A checked source read returns the scalar stored at the associated physical
index. The source answer is obtained from Array.index_usize_spec, not supplied
as a primitive-answer hypothesis. Read observations/ABI association remain P. -/
theorem array_read {n : Usize} (a : Array U8 n) (i : Usize)
    (w : State) (address : Nat) (hi : i.val < a.val.length)
    (hb : w.memory (address+i.val) =
      ((PV_EVH_StackEntropyFill.encode a)[i.val]?.getD 0).toNat) :
    ∃ x, Array.index_usize a i = .ok x ∧ w.memory (address+i.val) = x.val := by
  obtain ⟨x,hx,he⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hi)
  refine ⟨x,hx,PV_EVH_StackByteCodec.copied_read a w address i.val x hb ?_⟩
  rw [List.getElem?_eq_getElem hi]
  exact congrArg some he.symm

theorem first_encoding (a : Array U8 64#usize) (i : Nat) (hi : i < 32) :
    (PV_EVH_StackEntropyFill.encode (PV_EVH_EntropyHalves.field a))[i]? =
      (PV_EVH_StackEntropyFill.encode a)[i]? := by
  simp [PV_EVH_StackEntropyFill.encode,PV_EVH_EntropyHalves.field,
    List.getElem?_take,hi]

theorem second_encoding (a : Array U8 64#usize) (i : Nat) :
    (PV_EVH_StackEntropyFill.encode (PV_EVH_EntropyHalves.seed a))[i]? =
      (PV_EVH_StackEntropyFill.encode a)[32+i]? := by
  simp [PV_EVH_StackEntropyFill.encode,PV_EVH_EntropyHalves.seed]

theorem first_read (a : Array U8 64#usize) (i : Usize)
    (w : State) (address : Nat) (hi : i.val < 32)
    (hb : w.memory (address+i.val) =
      ((PV_EVH_StackEntropyFill.encode a)[i.val]?.getD 0).toNat) :
    ∃ x, Array.index_usize (PV_EVH_EntropyHalves.field a) i = .ok x ∧
      w.memory (address+i.val) = x.val := by
  apply array_read (PV_EVH_EntropyHalves.field a) i w address
    (by simpa only [(PV_EVH_EntropyHalves.field a).property] using hi)
  rw [first_encoding a i.val hi]
  exact hb

theorem second_read (a : Array U8 64#usize) (i : Usize)
    (w : State) (address : Nat) (hi : i.val < 32)
    (hb : w.memory (address+i.val) =
      ((PV_EVH_StackEntropyFill.encode a)[32+i.val]?.getD 0).toNat) :
    ∃ x, Array.index_usize (PV_EVH_EntropyHalves.seed a) i = .ok x ∧
      w.memory (address+i.val) = x.val := by
  apply array_read (PV_EVH_EntropyHalves.seed a) i w address
    (by simpa only [(PV_EVH_EntropyHalves.seed a).property] using hi)
  rw [second_encoding a i.val]
  exact hb

#print axioms array_read
#print axioms first_encoding
#print axioms second_encoding
#print axioms first_read
#print axioms second_read
end PV_EVH_EntropyCopiedRead
