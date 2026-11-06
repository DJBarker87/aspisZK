import PCC_Reference
set_option autoImplicit false
namespace PCC.Reference
open PCA

theorem bind_ok {α β : Type} (r : Reference α) (f : α → Reference β)
    (s : PCA_State) (x : α) (h : (r s).reply = .ok x) :
    bind r f s =
      ⟨(f x (r s).state).state, (r s).events ++ (f x (r s).state).events,
        (f x (r s).state).reply⟩ := by simp only [bind,h]

theorem bind_error {α β : Type} (r : Reference α) (f : α → Reference β)
    (s : PCA_State) (e : Failure) (h : (r s).reply = .error e) :
    bind r f s = ⟨(r s).state,(r s).events,.error e⟩ := by simp only [bind,h]

theorem bind_abort {α β : Type} (r : Reference α) (f : α → Reference β)
    (s : PCA_State) (e : String) (h : (r s).reply = .abort e) :
    bind r f s = ⟨(r s).state,(r s).events,.abort e⟩ := by simp only [bind,h]

#print axioms bind_ok
#print axioms bind_error
#print axioms bind_abort
end PCC.Reference
