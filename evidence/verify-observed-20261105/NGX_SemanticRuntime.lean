import NGX_SemanticNew
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NGX_SemanticRuntime
 theorem domain_bytes : r1_wire.DOMAIN = Array.to_slice (Array.make 38#usize [85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,58#u8,80#u8,82#u8,73#u8,86#u8,65#u8,84#u8,69#u8,45#u8,83#u8,65#u8,76#u8,84#u8,69#u8,68#u8,58#u8,83#u8,69#u8,77#u8,65#u8,78#u8,84#u8,73#u8,67#u8,58#u8,80#u8,51#u8]) := by unfold r1_wire.DOMAIN; rfl
 theorem domain_length : (Slice.len r1_wire.DOMAIN).val=38 := by unfold r1_wire.DOMAIN; rfl
 def seedViews (domain tag length pub root size : Nat) : List (Nat×Nat) :=
  [(domain,38),(tag,1),(length,4),(pub,size),(root,32)]
 theorem seed_domain (domain tag length pub root size : Nat) (bound : size≤57607) :
  (seedViews domain tag length pub root size).length≤9 ∧
  ∀ v∈seedViews domain tag length pub root size,v.2≤57607 := by
  constructor
  · change 5≤9;decide
  · intro v h
    simp only [seedViews,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
#print axioms domain_bytes
#print axioms domain_length
#print axioms seed_domain
end AspisR1.NGX_SemanticRuntime
