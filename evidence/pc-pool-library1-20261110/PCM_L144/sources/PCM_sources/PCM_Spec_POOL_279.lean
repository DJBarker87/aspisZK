import PCM_PageLaws
import PCM_Page
set_option autoImplicit false
namespace PCM_POOL_279
open RSL PCM PCM.Computation PCM.Page
abbrev Args := AccountInfo × Header × List Digest
def Domain (a : Args) : Prop := ∀ d ∈ a.2.2, d.length = 8
/-- debug_assert is absent in deployed optimized code; explicit writes and
all later bounds failures retain their prefixes. The u16 addition wraps in
this build; the normal caller proves filled+roots<=256 separately. -/
def Ref (a : Args) : Computation Unit := do
  let (account,header,roots) := a
  writeRoots account header.filled.toNat roots
  patch account 56 (le16 (header.filled + roots.length.toUInt16))
def RowSpec (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec Domain Ref impl

theorem avoids_wrong_error (a : Args) : PCM.Computation.Avoid .invalidArgument (Ref a) := by
  rcases a with ⟨account,header,roots⟩
  unfold Ref
  apply PCM.Computation.bind_avoid
  · exact PCM.Page.roots_avoid _ _ _ _
  · intro u; exact PCM.Page.patch_avoid _ _ _ _

theorem rejects_wrong_error (a : Args) (hd : Domain a) :
    ¬ RowSpec (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) :=
  PCM.rejects_avoided_error Domain Ref a hd .invalidArgument (avoids_wrong_error a)
#print axioms avoids_wrong_error
#print axioms rejects_wrong_error
end PCM_POOL_279
