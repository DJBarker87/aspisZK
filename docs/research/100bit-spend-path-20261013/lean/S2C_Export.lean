import S2C_Cleanup
set_option autoImplicit false
namespace AspisR1.S2C
open S2Trust

/-- Local obligations for the normal five-drop suffix, all indexed by the same
execution e and its consecutive cuts. These are OPEN source-refinement premises,
not a claim that native acceptance supplies a certificate. No output equality
or independently existential native run is a field. -/
structure TailAdmission {E W F : Type} (L : Library W F)
    (native : E → Nat → W) (e : E) (s : Heap F) (vec box : F → F)
    (proof pubGuard checkpoint : Guard) : Prop where
  vecStep : ∀ h, L.related (native e 0) h → L.related (native e 1) (ownerStep h vec)
  boxStep : ∀ h, L.related (native e 2) h → L.related (native e 3) (ownerStep h box)
  validProof : Valid (ownerStep s vec)
  foundProof : lookup (ownerStep s vec) proof.token = some proof
  kindProof : proof.kind = .shared
  positiveProof : 0 < s.counter proof.cell
  runProof : L.run (native e 1) (.drop proof.token) = (native e 2, .unit)
  validPublic : Valid (ownerStep (release (ownerStep s vec) proof) box)
  foundPublic : lookup (ownerStep (release (ownerStep s vec) proof) box) pubGuard.token = some pubGuard
  kindPublic : pubGuard.kind = .shared
  positivePublic : 0 < (release (ownerStep s vec) proof).counter pubGuard.cell
  runPublic : L.run (native e 3) (.drop pubGuard.token) = (native e 4, .unit)
  validCheckpoint : Valid (release (ownerStep (release (ownerStep s vec) proof) box) pubGuard)
  foundCheckpoint : lookup (release (ownerStep (release (ownerStep s vec) proof) box) pubGuard)
    checkpoint.token = some checkpoint
  kindCheckpoint : checkpoint.kind = .exclusive
  countCheckpoint : (release (ownerStep (release (ownerStep s vec) proof) box) pubGuard).counter checkpoint.cell = -1
  runCheckpoint : L.run (native e 4) (.drop checkpoint.token) = (native e 5, .unit)
  validFinal : Valid (cleanup s vec box proof pubGuard checkpoint)

/-- Copy and cleanup use one native cut map, with the cleanup map DEFINED by
shifting it by 1768. There is no separately selected successful continuation. -/
theorem same_execution_final_related {E W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (native : E → Nat → W)
    (initial : E → Heap F) (source : E → Nat → UInt8) (e : E)
    (g proof pubGuard checkpoint : Guard) (vec box : F → F)
    (related : L.related (native e 0) (initial e)) (valid : Valid (initial e))
    (found : lookup (initial e) g.token = some g) (kind : g.kind = .exclusive)
    (length : ((initial e).payload g.cell).descriptor.length = 1768)
    (actualCopy : ∀ i, i < 1768 →
      L.run (native e i) (.write g.token i (source e i)) = (native e (i+1), .unit))
    (tail : TailAdmission L (fun e k => native e (1768+k)) e
      (copyPrefix (initial e) g (source e) 1768) vec box proof pubGuard checkpoint) :
    L.related (native e 1773)
      (cleanup (copyPrefix (initial e) g (source e) 1768) vec box proof pubGuard checkpoint) := by
  have copied := native_copy_cuts L trust native initial source e g 1768
    related valid found kind length actualCopy 1768 (Nat.le_refl _)
  exact native_cleanup_cuts L trust (fun e k => native e (1768+k)) e _ vec box
    proof pubGuard checkpoint copied tail.vecStep tail.boxStep
    tail.validProof tail.foundProof tail.kindProof tail.positiveProof tail.runProof
    tail.validPublic tail.foundPublic tail.kindPublic tail.positivePublic tail.runPublic
    tail.validCheckpoint tail.foundCheckpoint tail.kindCheckpoint tail.countCheckpoint tail.runCheckpoint

/-- Export final CP bytes and original proof/public payloads, all allocation
geometry, and written metadata. This is a CONDITIONAL local composition law.
In particular `interpretsMetadata` is a runtime carrier interpretation; the
library's fifteen fields do not provide an ambient-state observation function.
It must not be silently included in SDK trust. -/
theorem same_execution_output {E W F M : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (native : E → Nat → W)
    (original initial : E → Heap F) (source : E → Nat → UInt8) (e : E)
    (g proof pubGuard checkpoint : Guard) (vec box : F → F)
    (metadata : F → M) (nativeMetadata : W → M)
    (interpretsMetadata : ∀ w h, L.related w h → nativeMetadata w = metadata h.ambient)
    (vecMeta : ∀ f, metadata (vec f) = metadata f)
    (boxMeta : ∀ f, metadata (box f) = metadata f)
    (prefixMeta : metadata (initial e).ambient = metadata (original e).ambient)
    (proofCell pubCell : Nat)
    (proofSeparate : proofCell ≠ g.cell) (publicSeparate : pubCell ≠ g.cell)
    (prefixProof : (initial e).payload proofCell = (original e).payload proofCell)
    (prefixPublic : (initial e).payload pubCell = (original e).payload pubCell)
    (prefixGeometry : ∀ c, ((initial e).payload c).descriptor = ((original e).payload c).descriptor)
    (related : L.related (native e 0) (initial e)) (valid : Valid (initial e))
    (found : lookup (initial e) g.token = some g) (kind : g.kind = .exclusive)
    (length : ((initial e).payload g.cell).descriptor.length = 1768)
    (actualCopy : ∀ i, i < 1768 →
      L.run (native e i) (.write g.token i (source e i)) = (native e (i+1), .unit))
    (tail : TailAdmission L (fun e k => native e (1768+k)) e
      (copyPrefix (initial e) g (source e) 1768) vec box proof pubGuard checkpoint) :
    (∀ i, i < 1768 → (L.cellPayload (native e 1773) g.cell).contents i = source e i) ∧
    L.cellPayload (native e 1773) proofCell = (original e).payload proofCell ∧
    L.cellPayload (native e 1773) pubCell = (original e).payload pubCell ∧
    (∀ c, (L.cellPayload (native e 1773) c).descriptor = ((original e).payload c).descriptor) ∧
    nativeMetadata (native e 1773) = metadata (original e).ambient := by
  have relatedFinal := same_execution_final_related L trust native initial source e
    g proof pubGuard checkpoint vec box related valid found kind length actualCopy tail
  have payload := trust.cell_payload _ _ relatedFinal tail.validFinal
  obtain ⟨cp,pf,pub⟩ := copy_cleanup_regions (original e) (initial e) g (source e)
    vec box proof pubGuard checkpoint proofCell pubCell proofSeparate publicSeparate prefixProof prefixPublic
  refine ⟨?_,(payload proofCell).trans pf,(payload pubCell).trans pub,?_,?_⟩
  · intro i hi
    exact (congrArg (fun p : Payload => p.contents i) (payload g.cell)).trans (cp i hi)
  · intro c
    exact (congrArg Payload.descriptor (payload c)).trans
      ((copy_descriptor (initial e) g (source e) 1768 c).trans (prefixGeometry c))
  · have copyAmbient := (copy_structural_frame (initial e) g (source e) 1768).2.2.2.2.2.2
    have copyMeta := congrArg metadata copyAmbient
    have dropMeta := cleanup_metadata (copyPrefix (initial e) g (source e) 1768)
      vec box metadata proof pubGuard checkpoint vecMeta boxMeta
    exact (interpretsMetadata _ _ relatedFinal).trans
      (dropMeta.trans (copyMeta.trans prefixMeta))

#print axioms same_execution_final_related
#print axioms same_execution_output
end AspisR1.S2C
