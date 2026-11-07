import PCM_PageLaws
import PCM_Page
set_option autoImplicit false
namespace PCM_POOL_286
open RSL PCM PCM.Computation PCM.Page
abbrev Args := AccountInfo × B32 × UInt64 × UInt64 × List Digest
/-- Representation clauses for Rust's fixed-width Digest elements. They do
not assume sufficient buffer capacity or successful completion. -/
def Domain (a : Args) : Prop := ∀ d ∈ a.2.2.2.2, d.length = 8

def Ref (a : Args) : Computation Unit := do
  let (account,pool,page,sequence,roots) := a
  let s ← get
  write account (List.replicate (s.bytes account).length 0)
  patch account 0 [65,83,80,82]
  patch account 4 [1]
  patch account 5 [8]
  patch account 6 [1]
  patch account 8 pool.bytes
  patch account 40 (u64le page)
  patch account 48 (u64le sequence)
  patch account 56 (le16 roots.length.toUInt16)
  writeRoots account 0 roots

def RowSpec (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec Domain Ref impl

theorem avoids_wrong_error (a : Args) : PCM.Computation.Avoid .invalidArgument (Ref a) := by
  rcases a with ⟨account,pool,page,sequence,roots⟩
  unfold Ref
  apply PCM.Computation.bind_avoid
  · exact PCM.Page.get_avoid _
  · intro s
    apply PCM.Computation.bind_avoid
    · exact PCM.Page.write_avoid _ _ _
    · intro u
      apply PCM.Computation.bind_avoid
      · exact PCM.Page.patch_avoid _ _ _ _
      · intro u
        apply PCM.Computation.bind_avoid
        · exact PCM.Page.patch_avoid _ _ _ _
        · intro u
          apply PCM.Computation.bind_avoid
          · exact PCM.Page.patch_avoid _ _ _ _
          · intro u
            apply PCM.Computation.bind_avoid
            · exact PCM.Page.patch_avoid _ _ _ _
            · intro u
              apply PCM.Computation.bind_avoid
              · exact PCM.Page.patch_avoid _ _ _ _
              · intro u
                apply PCM.Computation.bind_avoid
                · exact PCM.Page.patch_avoid _ _ _ _
                · intro u
                  apply PCM.Computation.bind_avoid
                  · exact PCM.Page.patch_avoid _ _ _ _
                  · intro u
                    apply PCM.Computation.bind_avoid
                    · exact PCM.Page.patch_avoid _ _ _ _
                    · intro u
                      exact PCM.Page.roots_avoid _ _ _ _

theorem rejects_wrong_error (a : Args) (hd : Domain a) :
    ¬ RowSpec (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) :=
  PCM.rejects_avoided_error Domain Ref a hd .invalidArgument (avoids_wrong_error a)
#print axioms avoids_wrong_error
#print axioms rejects_wrong_error
end PCM_POOL_286
