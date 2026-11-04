import NFB_PeerAudit
set_option autoImplicit false
namespace NFB_BindPair

theorem split {A B C : Type} (f : A → B → C) (p : A × B) :
 (match p with | (a,b)=>f a b)=f p.1 p.2 := by cases p;rfl
#print axioms split
end NFB_BindPair
