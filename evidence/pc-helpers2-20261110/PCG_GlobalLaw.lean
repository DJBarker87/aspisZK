import PCG_GlobalRef.Funs
import PCG_MarkerCodec
import NJZ_TreeParent
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace PCG_GlobalLaw
open NJZ_EmptyTree

def run (p : Digest → Digest → Digest) (r : Fin 8 → Digest) : Digest :=
 p (p (p (r 0) (r 1)) (p (r 2) (r 3)))
   (p (p (r 4) (r 5)) (p (r 6) (r 7)))

/-- CLOSED child packet at SAME values, with no child-output hypothesis. -/
theorem child (left right : Digest) (hl : Canonical left) (hr : Canonical right) :
 NJZ_TreeParent.reply left right = parent left right ∧
 Canonical (NJZ_TreeParent.reply left right) := by
 have h := NJZ_TreeParent.source left right left right
   (NJZ_TreeParent.reply left right) 1 hl hr ⟨rfl,rfl,rfl,rfl⟩
 exact ⟨h.1,h.2.2⟩

/-- Bottom-up seven-call composition; each domain follows from its own inputs. -/
theorem row_324 (roots : Fin 8 → Digest) (canonical : ∀ i, Canonical (roots i)) :
 run NJZ_TreeParent.reply roots = run parent roots ∧
 Canonical (run NJZ_TreeParent.reply roots) := by
 have a := child (roots 0) (roots 1) (canonical 0) (canonical 1)
 have b := child (roots 2) (roots 3) (canonical 2) (canonical 3)
 have c := child (roots 4) (roots 5) (canonical 4) (canonical 5)
 have d := child (roots 6) (roots 7) (canonical 6) (canonical 7)
 have e := child _ _ a.2 b.2
 have f := child _ _ c.2 d.2
 have g := child _ _ e.2 f.2
 constructor
 · simpa only [run,e.1,f.1,a.1,b.1,c.1,d.1] using g.1
 · exact g.2

/-- Exact ordered call-log association for the extracted safe reference. -/
theorem extracted (roots : Array (Array U32 8#usize) 8#usize)
 (replies : Array (Array U32 8#usize) 7#usize) :
 PCG_GlobalRef.compose roots replies = ok {
  left := Array.make 7#usize [roots.val[0]'(by have h := roots.property; scalar_tac),roots.val[2]'(by have h := roots.property; scalar_tac),roots.val[4]'(by have h := roots.property; scalar_tac),roots.val[6]'(by have h := roots.property; scalar_tac),
    replies.val[0]'(by have h := replies.property; scalar_tac),replies.val[2]'(by have h := replies.property; scalar_tac),replies.val[4]'(by have h := replies.property; scalar_tac)],
  right := Array.make 7#usize [roots.val[1]'(by have h := roots.property; scalar_tac),roots.val[3]'(by have h := roots.property; scalar_tac),roots.val[5]'(by have h := roots.property; scalar_tac),roots.val[7]'(by have h := roots.property; scalar_tac),
    replies.val[1]'(by have h := replies.property; scalar_tac),replies.val[3]'(by have h := replies.property; scalar_tac),replies.val[5]'(by have h := replies.property; scalar_tac)],
  out := replies.val[6]'(by have h := replies.property; scalar_tac),calls := 7#usize} := by
 simp (disch := scalar_tac) only [PCG_GlobalRef.compose,PCG_MarkerCodec.read,lift,bind_tc_ok]
 rfl

#print axioms child
#print axioms row_324
#print axioms extracted
end PCG_GlobalLaw
