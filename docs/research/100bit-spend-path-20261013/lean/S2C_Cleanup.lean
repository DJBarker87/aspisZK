import S2C_CopyExecution
set_option autoImplicit false
namespace AspisR1.S2C
open S2Trust

/-- Owner deallocation may change allocator state in Ambient. Its footprint on
the account heap is a separate local refinement, NEVER part of SDK trust. -/
def ownerStep {F : Type} (s : Heap F) (effect : F → F) : Heap F :=
  {s with ambient := effect s.ambient}

/-- Exact normal GOTO role order: Vec reply, Ref proof, Box statement,
Ref public, RefMut checkpoint. The fixed candidate array has no destructor. -/
def cleanup {F : Type} (s : Heap F) (vec box : F → F)
    (proof pubGuard checkpoint : Guard) : Heap F :=
  release (release (ownerStep (release (ownerStep s vec) proof) box) pubGuard) checkpoint

theorem cleanup_frame {F : Type} (s : Heap F) (vec box : F → F)
    (proof pubGuard checkpoint : Guard) :
    (cleanup s vec box proof pubGuard checkpoint).payload = s.payload ∧
    (cleanup s vec box proof pubGuard checkpoint).accounts = s.accounts ∧
    (cleanup s vec box proof pubGuard checkpoint).ownerLive = s.ownerLive ∧
    (cleanup s vec box proof pubGuard checkpoint).allocated = s.allocated ∧
    (cleanup s vec box proof pubGuard checkpoint).external = s.external ∧
    (cleanup s vec box proof pubGuard checkpoint).ambient = box (vec s.ambient) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Lamports, all account metadata, Rc identity/counts and live ownership may be
included in meta; allocator state may be omitted. Each owner must preserve meta
by its own checked dispatch law. The trust item does not prove those laws. -/
theorem cleanup_metadata {F M : Type} (s : Heap F) (vec box : F → F)
    (metadata : F → M) (proof pubGuard checkpoint : Guard)
    (vecMeta : ∀ f, metadata (vec f) = metadata f)
    (boxMeta : ∀ f, metadata (box f) = metadata f) :
    metadata (cleanup s vec box proof pubGuard checkpoint).ambient = metadata s.ambient :=
  (boxMeta (vec s.ambient)).trans (vecMeta s.ambient)

/-- Restore the two shared increments, even when proof/public cells alias.
Separation from the exclusive cell is a runtime geometry obligation. -/
theorem cleanup_counters {F : Type} (original s : Heap F) (vec box : F → F)
    (proof pubGuard checkpoint : Guard)
    (pk : proof.kind = .shared) (uk : pubGuard.kind = .shared)
    (ck : checkpoint.kind = .exclusive)
    (pc : proof.cell ≠ checkpoint.cell) (uc : pubGuard.cell ≠ checkpoint.cell)
    (initialCP : original.counter checkpoint.cell = 0)
    (counts : ∀ c, s.counter c = if c = checkpoint.cell then -1 else
      original.counter c + (if c = pubGuard.cell then 1 else 0) +
        (if c = proof.cell then 1 else 0)) :
    (cleanup s vec box proof pubGuard checkpoint).counter = original.counter := by
  funext c
  simp only [cleanup,release_counter,ownerStep,pk,uk,ck,reduceCtorEq,ite_true,ite_false]
  by_cases hc : c = checkpoint.cell
  · subst c
    simp only [eq_self_iff_true, ite_true, initialCP]
  · simp only [if_neg hc]
    by_cases hp : c = proof.cell <;> by_cases hu : c = pubGuard.cell
    all_goals simp only [hp,hu,ite_true,ite_false]
    all_goals have h := counts c
    all_goals simp only [hc,hp,hu,ite_true,ite_false] at h
    all_goals omega

/-- Compose only the five fixed successor cuts of e. Owner simulations are
explicit, separate from the fifteen trusted SDK fields. They must be supplied
for the actual Vec/Box native drop, with typed carrier/allocator interpretation.
No field here assumes final bytes or complete caller success. -/
theorem native_cleanup_cuts {E W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (native : E → Nat → W) (e : E)
    (s : Heap F) (vec box : F → F) (proof pubGuard checkpoint : Guard)
    (related : L.related (native e 0) s)
    (vecStep : ∀ h, L.related (native e 0) h →
      L.related (native e 1) (ownerStep h vec))
    (boxStep : ∀ h, L.related (native e 2) h →
      L.related (native e 3) (ownerStep h box))
    (validProof : Valid (ownerStep s vec))
    (foundProof : lookup (ownerStep s vec) proof.token = some proof)
    (kindProof : proof.kind = .shared) (positiveProof : 0 < s.counter proof.cell)
    (runProof : L.run (native e 1) (.drop proof.token) = (native e 2, .unit))
    (validPublic : Valid (ownerStep (release (ownerStep s vec) proof) box))
    (foundPublic : lookup (ownerStep (release (ownerStep s vec) proof) box)
      pubGuard.token = some pubGuard)
    (kindPublic : pubGuard.kind = .shared)
    (positivePublic : 0 < (release (ownerStep s vec) proof).counter pubGuard.cell)
    (runPublic : L.run (native e 3) (.drop pubGuard.token) = (native e 4, .unit))
    (validCheckpoint : Valid (release (ownerStep (release (ownerStep s vec) proof) box) pubGuard))
    (foundCheckpoint : lookup (release (ownerStep (release (ownerStep s vec) proof) box) pubGuard)
      checkpoint.token = some checkpoint)
    (kindCheckpoint : checkpoint.kind = .exclusive)
    (countCheckpoint : (release (ownerStep (release (ownerStep s vec) proof) box) pubGuard).counter checkpoint.cell = -1)
    (runCheckpoint : L.run (native e 4) (.drop checkpoint.token) = (native e 5, .unit)) :
    L.related (native e 5) (cleanup s vec box proof pubGuard checkpoint) := by
  have r1 := vecStep s related
  have r2 := shared_drop_cut L trust native e 1 _ proof r1 validProof foundProof
    kindProof positiveProof runProof
  have r3 := boxStep _ r2
  have r4 := shared_drop_cut L trust native e 3 _ pubGuard r3 validPublic foundPublic
    kindPublic positivePublic runPublic
  exact exclusive_drop_cut L trust native e 4 _ checkpoint r4 validCheckpoint foundCheckpoint
    kindCheckpoint countCheckpoint runCheckpoint

/-- Original proof/public snapshots survive copy plus this exact cleanup order.
This exports byte identity from the original heap, not a reread after native.
Prefix facts bind the copy cut to original external inputs and remain explicit. -/
theorem copy_cleanup_regions {F : Type} (original cut : Heap F) (g : Guard)
    (source : Nat → UInt8) (vec box : F → F) (proof pubGuard checkpoint : Guard)
    (proofCell pubCell : Nat)
    (proofSeparate : proofCell ≠ g.cell) (publicSeparate : pubCell ≠ g.cell)
    (proofPrefix : cut.payload proofCell = original.payload proofCell)
    (publicPrefix : cut.payload pubCell = original.payload pubCell) :
    let final := cleanup (copyPrefix cut g source 1768) vec box proof pubGuard checkpoint
    (∀ i, i < 1768 → (final.payload g.cell).contents i = source i) ∧
    final.payload proofCell = original.payload proofCell ∧
    final.payload pubCell = original.payload pubCell := by
  obtain ⟨cp,pf,pub,_⟩ := checkpoint_copy_regions cut g source proofCell pubCell
    proofSeparate publicSeparate
  exact ⟨cp,pf.trans proofPrefix,pub.trans publicPrefix⟩

#print axioms cleanup_frame
#print axioms cleanup_metadata
#print axioms cleanup_counters
#print axioms native_cleanup_cuts
#print axioms copy_cleanup_regions
end AspisR1.S2C
