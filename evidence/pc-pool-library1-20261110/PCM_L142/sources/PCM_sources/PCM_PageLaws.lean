import PCM_Page
import PCM_AvoidRejection
set_option autoImplicit false
namespace PCM.Page
open RSL Computation

theorem get_avoid (bad : ProgramError) : Avoid bad get := by
  intro s env s1 es h
  cases congrArg Observation.exit h

theorem write_avoid (bad : ProgramError) (account : AccountInfo) (bytes : Bytes) :
    Avoid bad (write account bytes) := by
  intro s env s1 es h
  unfold write at h
  split at h <;> cases congrArg Observation.exit h

theorem patch_avoid (bad : ProgramError) (account : AccountInfo) (offset : Nat) (bytes : Bytes) :
    Avoid bad (patch account offset bytes) := by
  unfold patch
  apply bind_avoid
  · exact get_avoid _
  · intro s
    split
    · exact write_avoid _ _ _
    · intro s1 env s2 es h
      cases congrArg Observation.exit h

theorem roots_avoid (bad : ProgramError) (account : AccountInfo) (slot : Nat) (roots : List Digest) :
    Avoid bad (writeRoots account slot roots) := by
  induction roots generalizing slot with
  | nil => exact pure_avoid _ _
  | cons root rest ih =>
    unfold writeRoots
    apply bind_avoid
    · exact patch_avoid _ _ _ _
    · intro u; exact ih _

#print axioms get_avoid
#print axioms write_avoid
#print axioms patch_avoid
#print axioms roots_avoid
end PCM.Page
