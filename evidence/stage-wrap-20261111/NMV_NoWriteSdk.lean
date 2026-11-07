import NMV_NoWrite
set_option autoImplicit false
namespace NMV_NoWriteSdk
open RSL NMV_NoWrite

theorem acquire_free (a : AccountInfo) (k : Kind) (s : SdkState) : Free (acquire a k s) := by
 unfold acquire
 split <;> apply bind_free
 all_goals first
 | apply emit_free; intro c b; intro h; cases h
 | intro _; exact pure_free _

theorem release_free (a : AccountInfo) (t : Nat) (k : Kind) (s : SdkState) : Free (release a t k s) := by
 apply bind_free
 · apply emit_free; intro c b h; cases h
 · intro _; exact pure_free _

theorem snapshot_free (a : AccountInfo) (x y : Nat) (s : SdkState) : Free (snapshot a x y s) := by
 apply bind_free _ _ (acquire_free a .shared s)
 intro r
 rcases r with ⟨res,s1⟩
 cases res with
 | error e => exact pure_free _
 | ok t =>
   apply bind_free
   · split
     · exact alloc_free
     · exact pure_free _
   · intro _
     apply bind_free _ _ (release_free a t .shared s1)
     intro _; exact pure_free _

theorem snapshots_free (as : List AccountInfo) (ls : List (Nat × Nat)) (s : SdkState) :
 Free (TX2_240.snapAll as ls s) := by
 induction as generalizing ls s with
 | nil => exact pure_free _
 | cons a as ih =>
   cases ls with
   | nil => exact pure_free _
   | cons l ls =>
     apply bind_free _ _ (snapshot_free a l.1 l.2 s)
     intro r
     apply bind_free _ _ (ih ls r.2)
     intro _; exact pure_free _

/-- No account-write event introduced by the wrapper itself. Child event
write-freeness remains a distinct property of its full library law. -/
theorem stage2_free
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (hc : ∀ a env c b, Event.write c b ∉ (child a env).events)
 (a : TX2_240.Args) (s : SdkState) : Free (NMV_RslFold.stage2 child a s) := by
 unfold NMV_RslFold.stage2
 split
 · exact pure_free _
 · apply bind_free
   · apply emit_free; intro c b h; cases h
   · intro _
     apply bind_free _ _ (snapshots_free _ _ s)
     intro r
     apply bind_free _ _ (env_free _)
     intro clock
     apply bind_free
     · apply emit_free; intro c b h; cases h
     · intro _
       apply bind_free
       · intro env o h c b
         change o=child _ env at h
         subst h
         exact hc _ env c b
       · intro _; exact pure_free _

#print axioms acquire_free
#print axioms release_free
#print axioms snapshot_free
#print axioms snapshots_free
#print axioms stage2_free
end NMV_NoWriteSdk
