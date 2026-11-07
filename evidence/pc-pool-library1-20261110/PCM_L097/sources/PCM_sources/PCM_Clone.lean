import PCM_Semantics
set_option autoImplicit false
namespace PCM.Computation
open RSL
/-- One AccountInfo::clone site. Rc cloning does not allocate; its overflow
abort is a stopped prefix. Strong counts are private representation state,
not account-data cells. This law deliberately supplies NO native Rc frame;
that association and the safe-count caller clause remain OPEN in the map. -/
def cloneHandle (a : AccountInfo) : Computation AccountInfo := fun s _ o =>
  o = ⟨.ret (.ok a,s),[]⟩ ∨ o = ⟨.abort,[]⟩

def cloneHandles : List AccountInfo → Computation (List AccountInfo)
  | [] => pure []
  | a::rest => do
    let a1 ← cloneHandle a
    let tail ← cloneHandles rest
    pure (a1::tail)
end PCM.Computation
