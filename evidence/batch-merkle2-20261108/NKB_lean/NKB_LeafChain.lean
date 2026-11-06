import NKB_DedupCut
import NKB_IndexFold

set_option autoImplicit false
namespace NKB_LeafChain
open Aeneas Aeneas.Std Result MultiproofConeRef AspisR1
open MultiproofConeLiveFold

/-- Source-order local post-leaf cuts. A rejected digest has no inserted suffix.
This support relation supplies no hash reply, oracle law, physical exporter or
whole-parent success; those remain separate obligations of the parent. -/
inductive Chain : List Leaf → reference.Scratch → Option reference.Scratch → Prop where
 | done (s : reference.Scratch) : Chain [] s (some s)
 | rejected (index : U32) (leaf : Array U8 32#usize) (rest : List Leaf)
     (s : reference.Scratch) (room : s.n.val<16)
     (cut : NKB_DedupCut.Cut s index leaf none) : Chain ((index,leaf)::rest) s none
 | next (index : U32) (leaf : Array U8 32#usize) (rest : List Leaf)
     (s after : reference.Scratch) (out : Option reference.Scratch)
     (room : s.n.val<16) (cut : NKB_DedupCut.Cut s index leaf (some after))
     (tail : Chain rest after out) : Chain ((index,leaf)::rest) s out

theorem source (leaves : List Leaf) (s : reference.Scratch) (out : Option reference.Scratch)
    (chain : Chain leaves s out) : fold leaves s=ok out := by
 induction chain with
 | done s => rfl
 | rejected index leaf rest s room cut =>
   simp only [fold,NKB_DedupCut.source s index leaf room none cut,bind_tc_ok]
 | next index leaf rest s after out room cut tail ih =>
   simp only [fold,NKB_DedupCut.source s index leaf room (some after) cut,bind_tc_ok,ih]

theorem cursor (leaves : List Leaf) (s after : reference.Scratch)
    (chain : Chain leaves s (some after)) : after.«at»=s.«at» := by
 generalize out : some after=value at chain
 induction chain generalizing after with
 | done s => cases out;rfl
 | rejected index leaf rest s room cut => cases out
 | next index leaf rest s mid final room cut tail ih =>
   exact (ih after out).trans (NKB_DedupCut.cursor s index leaf mid cut)

#print axioms source
#print axioms cursor
end NKB_LeafChain
