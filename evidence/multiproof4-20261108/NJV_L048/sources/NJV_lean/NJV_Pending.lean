import NJV_RowDomains
import NJP_AbortPrefix

set_option autoImplicit false
noncomputable section
namespace NJV_Pending
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

/-- Pending native child frame, BEFORE any reply/write. Occupied: NJV_K002/003;
sibling: NJP_K070/071 and K013..016 borrowed byte windows. The child's SAME
slice arguments determine q; no reply or returned Result is included.

Native source: evidence/multiproof4-20261108/NJV_multiproof.rs,
sha256 b56ba8df20906b3ad4112375af36a79e8d9e35fa7dcbdbfcc8bf173c85179701 (NJV_K002/003).
Assertion excerpts: `assert_eq!(idx[k],before_idx);`
`assert_eq!(val[k][j],before_val);assert_eq!(at,before_at);`
`assert_eq!(first[j],val[i][j]);assert_eq!(second[j],val[i+1][j]);`
Sibling source: evidence/multiproof3-20261108/NJP_frontier_cuts.rs,
sha256 d7437c9e40b56e1886d4441396d5bcea65cd3d53ff53ec893f1da382b88dcd51 (NJP_K070/071).
Excerpts: `assert_eq!(at,old_at+32);` and
`assert_eq!(idx[k],old_idx);assert_eq!(val[k][h],old_val);`
The borrowed bytes and ordered child arguments are supplied by the SAME-input
window/parent certificates, as NJV_CUTS.md specifies.
 -/
structure Cut (s : Scratch) (i length : Nat) (nodes : Nat → U8)
    (pending : Scratch) (q : Request) : Prop where
 active : i<s.n
 available : paired s i ∨ s.cursor+32≤length
 arguments : q=if paired s i then occupiedRequest s i else siblingRequest s i nodes
 indices : pending.indices=s.indices
 values : pending.values=s.values
 count : pending.n=s.n
 cursor : pending.cursor=if paired s i then s.cursor else s.cursor+32

theorem request (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s pending : Scratch) (i w : Nat) (q : Request) (cut : Cut s i length nodes pending q) :
 NJP_AbortPrefix.pending H 0 (node nodes length s i w)=some ([],q) := by
 by_cases both : paired s i
 · rw [NJP_AbortPrefix.occupied_pending H nodes length s i w cut.active both,
     cut.arguments,if_pos both]
 · have available := cut.available.resolve_left both
   rw [NJP_AbortPrefix.sibling_pending H nodes length s i w cut.active both available,
     cut.arguments,if_neg both]

theorem frame (nodes : Nat → U8) (length : Nat) (s pending : Scratch) (i : Nat) (q : Request)
    (cut : Cut s i length nodes pending q) :
 pending={s with cursor:=if paired s i then s.cursor else s.cursor+32} := by
 exact NJP_WriteCarrier.state_ext pending {s with cursor:=if paired s i then s.cursor else s.cursor+32}
   cut.indices cut.values cut.count cut.cursor

#print request
#print axioms request
#print frame
#print axioms frame
end NJV_Pending
end
