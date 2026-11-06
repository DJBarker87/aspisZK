import MultiproofConeLeafContent
import NJV_EntryABI

set_option autoImplicit false
noncomputable section
namespace NKB_DedupCut
open Aeneas Aeneas.Std Result MultiproofConeRef AspisR1
open MultiproofConePhysicalLive MultiproofConeLeafContent

/-- NKB_K007/K008, NKB_fragments.rs::dedup_fragment, is the exact frozen
candidate.rs immediate duplicate/write block. Its assertions compare the full
Result/count and arbitrary idx[j],val[j][k] to prestate or the single appended
cell. These constructors transcribe ONLY those asserted local poststates;
they contain no whole-function endpoint or successful-child premise.
Fragment file SHA256 34f19cab614c347508188695773df4cd01167821e896b7cba6f2de1de5689559.
Harness file SHA256 f1a688cfd707c7fd688fe683b2ab96332f3cc01fb5709fcad941ebaa83021af0.
Assertion excerpts: `assert_eq!(idx[j],if write{index}else{before_i[j]});`
`assert_eq!(val[j][k],expected);` and exact Result/count checks.
Final credited pair: NKB_K013/NKB_K014; no K004 credit. -/
inductive Cut (s : reference.Scratch) (index : U32) (leaf : Digest) :
    Option reference.Scratch → Prop where
 | duplicate (active : 0<s.n.val) (same : s.idx.val[s.n.val-1]! =index)
     (consistent : s.val.val[s.n.val-1]! =leaf) : Cut s index leaf (some s)
 | rejected (active : 0<s.n.val) (same : s.idx.val[s.n.val-1]! =index)
     (different : s.val.val[s.n.val-1]!≠leaf) : Cut s index leaf none
 | appended (fresh : ¬(0<s.n.val ∧ s.idx.val[s.n.val-1]! =index))
     (room : s.n.val<16) :
   Cut s index leaf (some {s with idx:=s.idx.set s.n index,val:=s.val.set s.n leaf,n:=UScalar.ofNat (s.n.val+1) (by scalar_tac)})

/-- Native local branch substitution equals the existing cohort leaf step,
including duplicate-error rejection and every inactive cell. -/
theorem source (s : reference.Scratch) (index : U32) (leaf : Digest)
    (room : s.n.val<16) (out : Option reference.Scratch) (cut : Cut s index leaf out) :
 reference.leaf_step s index leaf=ok out := by
 rw [MultiproofConeLeafContent.step_exact s index leaf room]
 cases cut with
 | duplicate active same consistent =>
   simp only [MultiproofConeLeafContent.next,active,same,and_self,consistent,if_true]
 | rejected active same different =>
   simp only [MultiproofConeLeafContent.next,active,same,and_self,if_true,if_neg different]
 | appended fresh cap => simp only [MultiproofConeLeafContent.next,if_neg fresh]

theorem cursor (s : reference.Scratch) (index : U32) (leaf : Digest)
    (after : reference.Scratch) (cut : Cut s index leaf (some after)) :
 after.«at»=s.«at» := by cases cut <;> rfl

#print axioms source
#print axioms cursor
end NKB_DedupCut
end
