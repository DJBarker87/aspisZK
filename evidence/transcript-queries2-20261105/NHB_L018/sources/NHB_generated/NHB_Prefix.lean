import NHB_Canonical
import NHB_Partition
set_option autoImplicit false
namespace AspisR1.NHB_Prefix
open Aeneas Aeneas.Std

def prefix (s : NGQ_SamplerTrace.State) (count : Usize) (bound : count.val≤22) : Array U32 count :=
  ⟨s.accepted.val.take count.val,by
    have size : s.accepted.val.length=22 := s.accepted.property
    simpa only [List.length_take,size,Nat.min_eq_left bound]⟩

theorem active_prefix (s : NGQ_SamplerTrace.State) (count : Usize) (bound : count.val≤22)
    (n : Nat) (active : n≤count.val) :
    (prefix s count bound).val.take n=s.accepted.val.take n := by
  change (s.accepted.val.take count.val).take n=s.accepted.val.take n
  simp only [List.take_take,Nat.min_eq_left active]

theorem canonical (s : NGQ_SamplerTrace.State) (count : Usize) (bound : count.val≤22)
    (initial : NHB_Canonical.State s) : ∀ w∈(prefix s count bound).val,w.val<262144 := by
  intro w member
  exact initial w (List.mem_of_mem_take member)

theorem member (s : NGQ_SamplerTrace.State) (count : Usize) (bound : count.val≤22)
    (n : Nat) (active : n≤count.val) (x : U32) :
    NHB_Membership.reference x ((prefix s count bound).val.take n)=
      NHB_Membership.reference x (s.accepted.val.take n) := by
  rw [active_prefix s count bound n active]

#print axioms active_prefix
#print axioms canonical
#print axioms member
end AspisR1.NHB_Prefix
