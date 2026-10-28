import NBR_BlockConstruct
import NBL_OpeningTrace
import NBR_VecAppend
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBR_OpeningConstruct
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NBL_BlockTrace
open AspisR1CurrentCaller.OriginalSerializerInstallation

/-- Construct every local opening observation from infallible digest replies
and the reached S2 view's actual root. No opening/scalar success is assumed. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (total : NBR_BlockConstruct.Total D)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (variant : view.variant=.S2) (root : Array U8 32#usize)
    (rootCall : view.folded_root=some root) (roundSize : view.round1.val.length=224) :
    Nonempty (NBL_OpeningTrace.Trace D sem view hash) := by
  obtain ⟨seed,seedCall⟩ := total hash (NBA_Transcript.seedParts sem.transcript.state)
  obtain ⟨gamma⟩ := NBR_BlockConstruct.scalar D total (⟨seed,hash⟩ : transcript.Transcript H)
    27#u8 view.y1 true (by decide)
  have serialize : NBA_Installed.actual.sampling.toBytes view.inactive=ok (expectedBytes view.inactive) := by
    rw [NBA_Installed.serializer_slot,sourceBytes_total]
  obtain ⟨kappa⟩ := NBR_BlockConstruct.scalar D total gamma.block.after
    28#u8 (Array.to_slice (expectedBytes view.inactive)) false (by decide)
  obtain ⟨alpha0⟩ := NBR_BlockConstruct.scalar D total kappa.block.after 29#u8 view.round0 false (by decide)
  obtain ⟨bytes1,appendRoot,bytesRoot⟩ := NBR_VecAppend.total
    (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root) (by
      change 0+root.val.length≤Usize.max
      rw [root.property]
      scalar_tac)
  have rootLen : bytes1.val.length=32 := by
    rw [bytesRoot]
    exact root.property
  obtain ⟨bytes2,appendRound,bytesRound⟩ := NBR_VecAppend.total bytes1 view.round1 (by
    change bytes1.val.length+view.round1.val.length≤Usize.max
    rw [rootLen,roundSize]
    scalar_tac)
  obtain ⟨alpha1⟩ := NBR_BlockConstruct.scalar D total alpha0.block.after
    30#u8 (alloc.vec.Vec.deref bytes2) false (by decide)
  exact ⟨⟨variant,seed,seedCall,gamma,expectedBytes view.inactive,serialize,
    kappa,alpha0,root,rootCall,bytes1,bytes2,appendRoot,appendRound,alpha1⟩⟩

#print axioms source
end AspisR1.NBR_OpeningConstruct
end
