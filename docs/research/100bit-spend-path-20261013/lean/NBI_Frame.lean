import NBE_Audit
import MultiproofConePhysicalLive
import MultiproofConePhysicalProgram

set_option autoImplicit false
namespace AspisR1.NBI_Frame
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalLive

/-- Arbitrary native single-write frames select one installed owned update.
All coordinates are required, including the unconsumed suffix. -/
theorem write_ext (s actual : reference.Scratch) (w : Usize) (parent : U32)
    (digest : MultiproofConePhysicalLive.Digest) (cursor : Usize)
    (wb : w.val < 16)
    (indices : ∀ j, j < 16 → actual.idx.val[j]! =
      if j = w.val then parent else s.idx.val[j]!)
    (values : ∀ j, j < 16 → actual.val.val[j]! =
      if j = w.val then digest else s.val.val[j]!) :
    actual.idx = s.idx.set w parent ∧ actual.val = s.val.set w digest := by
  constructor
  · apply Subtype.ext
    apply List.ext_getElem
    · exact actual.idx.property.trans (s.idx.set w parent).property.symm
    · intro j ha hb
      have jb : j < 16 := by have len : actual.idx.val.length = 16 := actual.idx.property; omega
      have h := indices j jb
      have len : s.idx.val.length = 16 := s.idx.property
      have target : (s.idx.set w parent).val[j]! =
          if j = w.val then parent else s.idx.val[j]! := by
        by_cases eq : j = w.val
        · subst j
          simp [Array.set_val_eq,List.getElem!_eq_getElem?_getD,
            List.getElem?_set_self (by omega : w.val < s.idx.val.length)]
        · simp [Array.set_val_eq,List.getElem!_eq_getElem?_getD,
            List.getElem?_set_ne (Ne.symm eq),eq]
      simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem ha,
        List.getElem?_eq_getElem hb,Option.getD_some] using h.trans target.symm
  · apply Subtype.ext
    apply List.ext_getElem
    · exact actual.val.property.trans (s.val.set w digest).property.symm
    · intro j ha hb
      have jb : j < 16 := by have len : actual.val.val.length = 16 := actual.val.property; omega
      have h := values j jb
      have target := MultiproofConePhysicalDigest.set_digest s w digest wb j jb
      simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem ha,
        List.getElem?_eq_getElem hb,Option.getD_some] using h.trans target.symm

/-- Overwriting only the consumed prefix preserves the complete unread tail.
This consumes the arbitrary-coordinate frame, not a whole-buffer native gate. -/
theorem unread_after_write (s : reference.Scratch) (w : Usize) (parent : U32)
    (digest : MultiproofConePhysicalLive.Digest) (cursor : Usize)
    (i : Nat) (wb : w.val < 16) (safe : w.val < i) (ib : i ≤ 16) :
    view {s with idx := s.idx.set w parent,val := s.val.set w digest,«at» := cursor}
      i (16-i) = view s i (16-i) :=
  unread s w parent digest cursor wb i (16-i) safe (by omega)

/-- The actual installed post-hash writer is total on the native write domain.
No caller result or poststate is supplied as a premise. -/
theorem finish_exact (s : reference.Scratch) (digest : MultiproofConePhysicalLive.Digest)
    (ni cursor : Usize) (index : U32) (w : Usize) (wb : w.val < 16) :
    ∃ parent nw,
      parent.val = index.val / 2 ∧ nw.val = w.val + 1 ∧
      MultiproofConePhysicalProgram.finish s digest ni cursor index w =
        ok (.Next {s with idx := s.idx.set w parent,val := s.val.set w digest,«at» := cursor} ni nw) := by
  have spec : MultiproofConePhysicalProgram.finish s digest ni cursor index w
      ⦃ out => ∃ parent nw, parent.val = index.val / 2 ∧ nw.val = w.val + 1 ∧
        out = reference.Row.Next
          {s with idx := s.idx.set w parent,val := s.val.set w digest,«at» := cursor} ni nw ⦄ := by
    unfold MultiproofConePhysicalProgram.finish
    step*
  obtain ⟨out,returned,parent,nw,pv,nwv,eq⟩ := WP.spec_imp_exists spec
  exact ⟨parent,nw,pv,nwv,eq ▸ returned⟩

#print axioms write_ext
#print axioms unread_after_write
#print axioms finish_exact
end AspisR1.NBI_Frame
