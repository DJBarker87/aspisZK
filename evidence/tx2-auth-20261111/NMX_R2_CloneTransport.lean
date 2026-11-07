import NMX_R2_HeterogeneousPrimitives
set_option autoImplicit false
namespace NMX_R2_CloneTransport
open RSL
/-- A stopped clone carries only its empty event prefix, at the reached error
clone site. The same error value survives the returning arm. -/
theorem thrown {A B : Type} (encode : A → B) (e : ProgramError) :
 NMX_R2_Heterogeneous.Refines encode (RS.throw e) (RS.throw e) := by
 intro env o run
 change o = ⟨.ret (.error e),[]⟩ at run
 subst o
 rfl

theorem error {A B : Type} (encode : A → B) (e : ProgramError) :
 NMX_R2_Heterogeneous.Refines encode
  (RS.ofCloned (.error e)) (RS.ofCloned (.error e)) := by
 unfold RS.ofCloned
 split
 · apply NMX_R2_Heterogeneous.bind id encode
   · exact NMX_R2_HeterogeneousPrimitives.refl _
   · intro _
     exact thrown encode e
 · exact thrown encode e
#print axioms thrown
#print axioms error
end NMX_R2_CloneTransport
