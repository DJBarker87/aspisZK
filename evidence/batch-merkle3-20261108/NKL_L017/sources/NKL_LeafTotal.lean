import NKB_LeafChain
set_option autoImplicit false
noncomputable section
namespace NKL_LeafTotal
open Aeneas Aeneas.Std Result MultiproofConeRef AspisR1
open MultiproofConeLiveFold
attribute [local instance] Classical.propDecidable

/-- Every finite native insertion stream has a complete cut chain, including
its first inconsistent duplicate. No digest-consistency/success premise. -/
theorem total (leaves : List Leaf) (s : reference.Scratch)
 (room : s.n.val+leaves.length≤16) :
 ∃ out, NKB_LeafChain.Chain leaves s out := by
 induction leaves generalizing s with
 | nil => exact ⟨some s,.done s⟩
 | cons leaf rest ih =>
   rcases leaf with ⟨index,digest⟩
   have cap : s.n.val<16 := by simp only [List.length_cons] at room;omega
   by_cases same : 0<s.n.val ∧ s.idx.val[s.n.val-1]! = index
   · by_cases consistent : s.val.val[s.n.val-1]! = digest
     · obtain ⟨out,tail⟩:=ih s (by simp only [List.length_cons] at room;omega)
       exact ⟨out,.next index digest rest s s out cap
         (.duplicate same.1 same.2 consistent) tail⟩
     · exact ⟨none,.rejected index digest rest s cap (.rejected same.1 same.2 consistent)⟩
   · let next : reference.Scratch := {s with idx:=s.idx.set s.n index,
       val:=s.val.set s.n digest,n:=UScalar.ofNat (s.n.val+1) (by scalar_tac)}
     have advance : next.n.val=s.n.val+1 := rfl
     obtain ⟨out,tail⟩:=ih next (by simp only [List.length_cons] at room;omega)
     exact ⟨out,.next index digest rest s next out cap (.appended same cap) tail⟩

theorem source (leaves : List Leaf) (s : reference.Scratch)
 (room : s.n.val+leaves.length≤16) :
 ∃ out,NKB_LeafChain.Chain leaves s out ∧ fold leaves s=ok out := by
 obtain ⟨out,chain⟩:=total leaves s room
 exact ⟨out,chain,NKB_LeafChain.source leaves s out chain⟩

set_option pp.proofs false
#print total
#print axioms total
#print axioms source
end NKL_LeafTotal
end
