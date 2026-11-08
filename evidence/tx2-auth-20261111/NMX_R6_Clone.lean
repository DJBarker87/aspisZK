import NMX_R6_Observation
set_option autoImplicit false
namespace NMX_R6_Clone
open RSL NMX_R6_Observation

/-- A successful std clone returns its exact input, even for heap errors. The
full source relation still retains the independent abort at a nonempty String. -/
theorem member {A : Type} (r : Except ProgramError A) (env : Env) :
 RS.ofCloned r env ⟨.ret r,[]⟩ := by
 cases r with
 | ok a => rfl
 | error e =>
   simp only [RS.ofCloned]
   split
   · change Spec.bind (Spec.map Except.ok Spec.alloc) _ env _
     apply Or.inl
     refine ⟨Except.ok (),[],⟨.ret (.error e),[]⟩,?_,rfl,rfl⟩
     exact Or.inl ⟨(),[],⟨.ret (Except.ok ()),[]⟩,Or.inl rfl,rfl,rfl⟩
   · rfl
#print axioms member
end NMX_R6_Clone
