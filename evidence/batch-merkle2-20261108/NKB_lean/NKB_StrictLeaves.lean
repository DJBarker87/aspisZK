import NKB_LeafChain
import NKB_StrictCount

set_option autoImplicit false
noncomputable section
namespace NKB_StrictLeaves
open Aeneas Aeneas.Std Result MultiproofConeRef AspisR1
open MultiproofConeLiveFold MultiproofConeLivePreservation

/-- Exact arbitrary-digest strict stream: no duplicate error occurs, every
native local cut is a fresh append, and the resulting count is the full length.
This concerns the post-hash insertion loop only, not the complete batch root. -/
theorem total (leaves : List Leaf) (s : reference.Scratch)
    (room : s.n.val+leaves.length≤16)
    (ordered : (leaves.map (fun x => x.1.val)).Pairwise (·<·))
    (future : ∀ a,a<s.n.val → ∀ leaf∈leaves,keys s a<leaf.1.val) :
 ∃ after, NKB_LeafChain.Chain leaves s (some after) ∧ after.n.val=s.n.val+leaves.length := by
 induction leaves generalizing s with
 | nil => exact ⟨s,.done s,by simp⟩
 | cons leaf rest ih =>
   rcases leaf with ⟨index,digest⟩
   have cap : s.n.val<16 := by simp only [List.length_cons] at room;omega
   obtain ⟨head,tail⟩ := List.pairwise_cons.mp ordered
   have fresh : ¬(0<s.n.val ∧ s.idx.val[s.n.val-1]! =index) := by
     rintro ⟨positive,same⟩
     have less := future (s.n.val-1) (by omega) (index,digest) (by simp)
     change s.idx.val[s.n.val-1]!.val < index.val at less
     rw [same] at less
     omega
   let next : reference.Scratch := {s with idx:=s.idx.set s.n index,val:=s.val.set s.n digest,n:=UScalar.ofNat (s.n.val+1) (by scalar_tac)}
   have cut : NKB_DedupCut.Cut s index digest (some next) := .appended fresh cap
   have step := NKB_DedupCut.source s index digest cap (some next) cut
   have projection := MultiproofConeLiveBatch.leaf_projection s index digest cap next step
   have natfresh : ¬(0<s.n.val ∧ keys s (s.n.val-1)=index.val) := by
     rintro ⟨positive,same⟩
     have less := future (s.n.val-1) (by omega) (index,digest) (by simp)
     change keys s (s.n.val-1) < index.val at less
     omega
   have first := congrArg Prod.fst projection
   have second := congrArg Prod.snd projection
   change keys next=(MultiproofConeLiveLeaves.insert (keys s) s.n.val index.val).1 at first
   change next.n.val=(MultiproofConeLiveLeaves.insert (keys s) s.n.val index.val).2 at second
   simp only [MultiproofConeLiveLeaves.insert,if_neg natfresh] at first second
   have following : ∀ a,a<next.n.val → ∀ leaf∈rest,keys next a<leaf.1.val := by
     intro a bound leaf member
     rw [first]
     by_cases same : a=s.n.val
     · simp only [if_pos same]
       apply head leaf.1.val
       exact List.mem_map.mpr ⟨leaf,member,rfl⟩
     · simp only [if_neg same]
       exact future a (by omega) leaf (by simp only [List.mem_cons];exact Or.inr member)
   obtain ⟨after,chain,count⟩ := ih next (by simp only [List.length_cons] at room;omega) tail following
   refine ⟨after,.next index digest rest s next (some after) cap cut chain,?_⟩
   simp only [List.length_cons]
   omega

/-- No successful-child premise: every digest stream with TX2's twelve distinct
indices admits the native append-cut chain and has count twelve, not <=10. -/
theorem twelve (leaves : List Leaf) (s : reference.Scratch) (empty : s.n.val=0)
    (indices : leaves.map (fun x => x.1.val)=NKB_StrictCount.tx2Indices) :
 ∃ after, NKB_LeafChain.Chain leaves s (some after) ∧ after.n.val=12 ∧ ¬after.n.val≤10 := by
 have len : leaves.length=12 := by
   have h:=congrArg List.length indices
   simpa only [List.length_map,NKB_StrictCount.tx2Indices,List.length_range] using h
 have order : (leaves.map (fun x => x.1.val)).Pairwise (·<·) := by rw [indices];exact NKB_StrictCount.ordered
 obtain ⟨after,chain,count⟩ := total leaves s (by omega) order (by intro a impossible;omega)
 exact ⟨after,chain,by omega,by omega⟩

#print axioms total
#print axioms twelve
end NKB_StrictLeaves
end
