import NCE_OpeningRead
import NBY_RowCarrier

set_option autoImplicit false
namespace AspisR1.NCE_RowStoreCuts
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts
abbrev Digest := MultiproofConePhysicalLive.Digest
abbrev Store := Carrier → Usize → U32 → Digest → Usize → Carrier

/-- ONE post-hash index store plus selected digest write window. The digest
is the arbitrary ACTUAL runtime reply. Each arbitrary j/c observation frames
the exterior, and each non-scratch caller field is unchanged. This is not a
whole verifier, row-loop, precomputed root or successful-node assumption. -/
def NCE_Native_RowStore (native : Store) : Prop :=
  ∀ s w parent digest cursor, w.val < 16 →
    (native s w parent digest cursor).prepared = s.prepared ∧
    (native s w parent digest cursor).proof = s.proof ∧
    (native s w parent digest cursor).log = s.log ∧
    (native s w parent digest cursor).scratch.n = s.scratch.n ∧
    (native s w parent digest cursor).scratch.«at» = cursor ∧
    (∀ j, j < 16 → (native s w parent digest cursor).scratch.idx.val[j]! =
      if j = w.val then parent else s.scratch.idx.val[j]!) ∧
    (∀ j c, j < 16 → c < 32 →
      (native s w parent digest cursor).scratch.val.val[j]!.val[c]! =
        if j = w.val then digest.val[c]! else s.scratch.val.val[j]!.val[c]!)

/-- Reconstruct only ONE row value from byte observations. The imported NBI
frame theorem then identifies the actual cohort's single array assignment. -/
theorem store_eq (native : Store) (cut : NCE_Native_RowStore native)
    (s : Carrier) (w : Usize) (parent : U32) (digest : Digest) (cursor : Usize)
    (bound : w.val < 16) :
    native s w parent digest cursor = {s with scratch := {s.scratch with idx := s.scratch.idx.set w parent, val := s.scratch.val.set w digest, «at» := cursor}} := by
  obtain ⟨prepared,proof,log,n,cursorValue,indices,bytes⟩ := cut s w parent digest cursor bound
  let out := native s w parent digest cursor
  have values : ∀ j, j < 16 → out.scratch.val.val[j]! =
      if j = w.val then digest else s.scratch.val.val[j]! := by
    intro j jb
    apply Subtype.ext
    apply List.ext_getElem
    · exact out.scratch.val.val[j]!.property.trans
        (if j = w.val then digest else s.scratch.val.val[j]!).property.symm
    · intro c ha hb
      have len : out.scratch.val.val[j]!.val.length = 32 := out.scratch.val.val[j]!.property
      have cb : c < 32 := by omega
      have value : out.scratch.val.val[j]!.val[c]! =
          (if j = w.val then digest else s.scratch.val.val[j]!).val[c]! := by
        by_cases selected : j = w.val
        · simpa only [if_pos selected] using bytes j c jb cb
        · simpa only [if_neg selected] using bytes j c jb cb
      have left := getElem!_pos (out.scratch.val.val[j]!).val c ha
      have right := getElem!_pos (if j = w.val then digest else s.scratch.val.val[j]!).val c hb
      exact left.symm.trans (value.trans right)
  have arrays := NBI_Frame.write_ext s.scratch out.scratch w parent digest cursor bound indices values
  have scratch : out.scratch =
      {s.scratch with idx:=s.scratch.idx.set w parent,val:=s.scratch.val.set w digest,«at»:=cursor} := by
    change reference.Scratch.mk out.scratch.idx out.scratch.val out.scratch.n out.scratch.«at» =
      reference.Scratch.mk (s.scratch.idx.set w parent) (s.scratch.val.set w digest) s.scratch.n cursor
    congr 1 <;> first | exact arrays.1 | exact arrays.2 | exact n | exact cursorValue
  change Carrier.mk out.prepared out.proof out.scratch out.log =
    Carrier.mk s.prepared s.proof _ s.log
  congr 1 <;> first | exact prepared | exact proof | exact scratch | exact log

/-- The value installed by the single native row store is the SAME value as
the existing KMX one-byte windows, including every outside coordinate.
This consumes NBY's existing value law rather than re-proving copy semantics. -/
theorem stored_bytes (native : Store) (cut : NCE_Native_RowStore native)
    (s : Carrier) (w : Usize) (parent : U32) (digest : Digest) (cursor : Usize)
    (bound : w.val < 16) (j c : Nat) (jb : j < 16) (cb : c < 32) :
    (native s w parent digest cursor).scratch.val.val[j]!.val[c]! =
      NBY_RowCopy.byteWindows (fun k => digest.val[k-32*w.val]!)
        (NBY_RowCarrier.memory s.scratch) (32*w.val) 32 (32*j+c) := by
  rw [store_eq native cut s w parent digest cursor bound]
  exact (NBY_RowCarrier.installed_bytes s.scratch w digest j c bound jb cb).symm

#print axioms store_eq
#print axioms stored_bytes
end AspisR1.NCE_RowStoreCuts
