import AllAddressCollisionTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_CollisionOrder
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw

/-- Tiny diagnostic for a proposed generic sublist transport. This is NOT an
Aspis-source counterexample: the real prefix/inserted queries need their own
address/order proof. It rules out charging by sublist inclusion alone. -/
def pred (_ : Fin 1) (b : Bool) : Option (Fin 3) := if b=false then some 2 else none

def oldTrace : List (Bool × Fin 3) := [(false,1),(true,2)]
def enlargedTrace : List (Bool × Fin 3) := [(true,2),(false,1),(true,2)]

theorem old_hit : hitsBad (AllAddressCollision.bad (0 : Fin 3) pred 3) emptyTable oldTrace := by
  change _ ∨ _
  right
  change _ ∨ _
  left
  refine ⟨rfl,?_,?_⟩
  · refine ⟨{false},by decide,?_⟩
    intro b defined
    cases b with
    | false => simp
    | true => simp [put,emptyTable] at defined
  · exact Or.inr (Or.inr ⟨0,false,Or.inr (by simp [put]),rfl⟩)

theorem enlarged_clean : ¬ hitsBad (AllAddressCollision.bad (0 : Fin 3) pred 3) emptyTable enlargedTrace := by
  simp [enlargedTrace,hitsBad,AllAddressCollision.bad,pred,emptyTable,put,Bool.exists_bool]

theorem sublist : oldTrace.Sublist enlargedTrace := by
  exact List.Sublist.cons _ (List.Sublist.refl _)

theorem no_generic_sublist_transport : ¬ (∀ left right : List (Bool × Fin 3),
    left.Sublist right → hitsBad (AllAddressCollision.bad (0 : Fin 3) pred 3) emptyTable left →
      hitsBad (AllAddressCollision.bad (0 : Fin 3) pred 3) emptyTable right) := by
  intro transport
  exact enlarged_clean (transport oldTrace enlargedTrace sublist old_hit)

#print axioms old_hit
#print axioms enlarged_clean
#print axioms sublist
#print axioms no_generic_sublist_transport
end AspisR1.PFin_CollisionOrder
end
