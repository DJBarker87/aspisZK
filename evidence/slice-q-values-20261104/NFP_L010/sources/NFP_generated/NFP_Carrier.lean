import NFP_DotInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_Carrier
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts
/-- Reuse the headline adapter. No alternate emitted carrier is installed. -/
theorem from_to (value : E) : FIo_Install.fromE (FIo_Install.toE value) = value := rfl

theorem to_from (value : NEV_DotCarrier.NE) :
 FIo_Install.toE (FIo_Install.fromE value) = value := rfl

theorem words (value : E) :
 (FIo_Install.toE value).c0.c0.a=value.c0.c0.a ∧
 (FIo_Install.toE value).c0.c0.b=value.c0.c0.b ∧
 (FIo_Install.toE value).c0.c1.a=value.c0.c1.a ∧
 (FIo_Install.toE value).c0.c1.b=value.c0.c1.b ∧
 (FIo_Install.toE value).c1.c0.a=value.c1.c0.a ∧
 (FIo_Install.toE value).c1.c0.b=value.c1.c0.b ∧
 (FIo_Install.toE value).c1.c1.a=value.c1.c1.a ∧
 (FIo_Install.toE value).c1.c1.b=value.c1.c1.b :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem canonical (g : Array E 29#usize)
 (h : ∀ value∈g.val, NEV_DotCarrier.canonE (FIo_Install.toE value)) :
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g) := by
 intro value member
 obtain ⟨original,member,rfl⟩ := List.mem_map.mp member
 exact h original member
#print axioms from_to
#print axioms to_from
#print axioms words
#print axioms canonical
end AspisR1.NFP_Carrier
end
