import PV_EVHB_OwnerRegistry
/-! Commuting source-store/returning-registry diagrams. These are explicit
world equalities derived from source stores, not compatibility fields. Native
primitive and original caller association remain separate obligations. -/
set_option autoImplicit false
namespace PV_EVHB_RegistryStores
open R1Z.PV_FXM_ReserveWorld PV_EVHB_RawVecOwner PV_EVHB_OwnerRegistry

theorem project_denial {S F : Type} (owner : Nat) (w : NativeWorld S F)
    (h : Header) (cap : Nat) (backend : S) :
    project owner (denied w h cap backend)=
      attempted (request h cap) none
        (afterAnswer (request h cap) none ⟨backend,w.allocator.metadata⟩ (fromSource owner w))
        (project owner w) := rfl

theorem project_installed_allocation {S F : Type} (owner : Nat) (w : NativeWorld S F)
    (h : Header) (pointer cap : Nat) (backend : S) (sized : h.shape.width≠0) :
    project owner (install (allocated w h pointer cap backend) owner h pointer cap)=
      succeeded (request h cap) pointer
        (attempted (request h cap) (some pointer)
          (afterAnswer (request h cap) (some pointer)
            ⟨backend,resizedMetadata w.allocator h pointer cap⟩ (fromSource owner w))
          (project owner w)) := by
  have tables := source_install_table owner (allocated w h pointer cap backend)
    h pointer cap sized
  dsimp only [project,fromSource,allocated,succeeded,attempted,install,store,afterAnswer]
  congr 1
  congr 1
  exact tables

#print axioms project_denial
#print axioms project_installed_allocation
end PV_EVHB_RegistryStores
