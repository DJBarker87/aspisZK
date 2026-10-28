import PV_L2D_PublicationIndices
import PV_L2D_MerkleCost
set_option autoImplicit false
namespace PV_L2D_PublicationCaps
open PV_L2D_PublicationIndices PV_L2D_MerklePlan PV_L2D_MerkleCost

theorem member_source (queries : List Nat) (begin_ end_ : Nat) (folded : Bool) (z : Nat)
    (hz : z∈publication queries begin_ end_ folded) :
    ∃ q ∈ queries, z=(if folded then q/4 else q) := by
  obtain h | h := (build_mem [] (((queries.drop begin_).take (end_-begin_)).map
    (fun q => if folded then q/4 else q)) z).mp hz
  · simp at h
  · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact ⟨q,List.mem_of_mem_drop (List.mem_of_mem_take hq),rfl⟩
#print axioms member_source

theorem ordinary_domain (queries : List Nat) (begin_ end_ : Nat)
    (domain : ∀ q ∈ queries, q<2^18) :
    ∀ z∈publication queries begin_ end_ false, z<2^18 := by
  intro z hz
  obtain ⟨q,hq,he⟩ := member_source queries begin_ end_ false z hz
  simpa [he] using domain q hq
#print axioms ordinary_domain

theorem folded_domain (queries : List Nat) (begin_ end_ : Nat)
    (domain : ∀ q ∈ queries, q<2^18) :
    ∀ z∈publication queries begin_ end_ true, z<2^16 := by
  intro z hz
  obtain ⟨q,hq,he⟩ := member_source queries begin_ end_ true z hz
  have hq := domain q hq
  norm_num at hq ⊢
  simp only [Bool.true_eq,ite_true] at he
  omega
#print axioms folded_domain

def begin_ (batch : Bool) := if batch then 10 else 0
def end_ (batch : Bool) := if batch then 22 else 10
def cap (batch folded : Bool) :=
  if folded then (if batch then 150 else 128) else (if batch then 172 else 146)

theorem all_slots (queries : List Nat) (batch folded : Bool) (depth : Nat)
    (domain : ∀ q ∈ queries, q<2^18) :
    (plan 18 depth (publication queries (begin_ batch) (end_ batch) folded)).length≤cap batch folded := by
  have hs := publication_length queries (begin_ batch) (end_ batch) folded
  have ho := publication_ordered queries (begin_ batch) (end_ batch) folded
  cases folded with
  | false =>
    have h:=ordinary_cap _ _ depth hs ho (ordinary_domain queries _ _ domain)
    cases batch <;> simpa [begin_,end_,cap] using h
  | true =>
    have h:=folded_cap _ _ depth hs ho (folded_domain queries _ _ domain)
    cases batch <;> simpa [begin_,end_,cap] using h
#print axioms all_slots

theorem fixed_padding (queries : List Nat) (batch folded : Bool) (depth : Nat)
    (domain : ∀ q ∈ queries, q<2^18) (read : Address → Digest) (header : List UInt8) :
    let nodes := (emit read (plan 18 depth
      (publication queries (begin_ batch) (end_ batch) folded))).1
    (header ++ nodes ++ List.replicate (32*cap batch folded-nodes.length) 0).length =
      header.length+32*cap batch folded := by
  dsimp only
  have h:=all_slots queries batch folded depth domain
  have hn : (emit read (plan 18 depth
      (publication queries (begin_ batch) (end_ batch) folded))).1.length≤32*cap batch folded := by
    rw [emitted_length]
    omega
  simp only [List.length_append,List.length_replicate]
  omega
#print axioms fixed_padding
end PV_L2D_PublicationCaps
