import NGP_L159
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIN_GameProjection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical

/-- Exact remaining external association, NOT a trust row and NOT assumed by
any NIN theorem. External projections must be pinned by D188/native producers.
Identifying two arbitrary Observations records is not such a producer. -/
def PhysicalRealization {Tx A : Type} (p : CPG_Projection.Observations Tx A)
    (actualNext : Tx → Tx → Prop)
    (actualBefore actualTentative : Tx → Nat → CPR_DataPersistence.Image)
    (actualSuccess : Tx → Bool) (actualLoaded : Tx → Nat → Option Bytes)
    (actualActions : Tx → List (CPP_BankState.Action A))
    (actualEvents : Tx → List S2X.AccountEvent)
    (actualLayout : Tx → Hist_RuntimeEntry.Layout) : Prop :=
  (∀ t u, p.next t u ↔ actualNext t u) ∧
  (∀ t key, CPG_Projection.before p t key = actualBefore t key) ∧
  (∀ t key, CPG_Projection.tentative p t key = actualTentative t key) ∧
  (∀ t, CPG_Projection.success p t = actualSuccess t) ∧
  (∀ t key, CPG_Projection.loaded p t key = actualLoaded t key) ∧
  (∀ t, p.actions t = actualActions t) ∧
  (∀ t, p.physicalEvents t = actualEvents t) ∧
  (∀ t, p.layout t = actualLayout t)

/-- The game itself provides the internal SAME-entry association, including
public checkpoint key as well as global index. This supplies no external bank
implementation or Pool invocation absent from the game's type. -/
theorem game_fields {Tx A : Type}
    (p : CPG_Projection.Observations Tx A) (t u : Tx) (e1 e2 : Entry)
    (saved : alloc.vec.Vec U8) (actions : List (CPP_BankState.Action A))
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id) :
    p.next t u ∧ e1 = CPG_Projection.entry p t ∧ e2 = CPG_Projection.entry p u ∧
    ((p.layout t).handles 2).1 = ((p.layout u).handles 6).1 ∧
    CPS_PhysicalKey.key e1 2 = CPS_PhysicalKey.key e2 6 ∧
    CPG_Projection.success p t = true ∧ p.copied t = saved ∧ p.actions t = actions :=
  ⟨game.consecutive.1,game.consecutive.2.1,game.consecutive.2.2,
    game.checkpoint.1,game.checkpoint.2.1,game.parent,game.recorded.1.1,game.recorded.1.2.1⟩

/-- These are exactly how model bank/layout/read observations are projected;
no stronger funding, owner or runtime-equality law is being inferred. -/
theorem bank_images {Tx A : Type} (p : CPG_Projection.Observations Tx A) (t : Tx) (key : Nat) :
    CPG_Projection.before p t key = CPR_DataPersistence.snapshot (p.bank t) key ∧
    CPG_Projection.tentative p t key = CPR_DataPersistence.snapshot (p.parentTentative t) key ∧
    CPG_Projection.loaded p t key = CPR_DataPersistence.visible (CPG_Projection.before p t key) ∧
    CPG_Projection.success p t = CPS_ParentStatus.success (p.parentReply t) := ⟨rfl,rfl,rfl,rfl⟩
/-- An unassociated external status can disagree with p even when every model
projection is fixed. This is a logical independence witness, not a claim that
Solana returns an inverted status. It cannot be repaired by choosing p twice. -/
theorem external_status_independent {Tx A : Type}
    (p : CPG_Projection.Observations Tx A) (t : Tx) :
    ¬ PhysicalRealization p p.next (CPG_Projection.before p) (CPG_Projection.tentative p)
      (fun u => !(CPG_Projection.success p u)) (CPG_Projection.loaded p)
      p.actions p.physicalEvents p.layout := by
  intro associated
  have h := associated.2.2.2.1 t
  cases status : CPG_Projection.success p t <;> simp only [status, Bool.not_false, Bool.not_true] at h
#print axioms external_status_independent
#print axioms game_fields
#print axioms bank_images
end AspisR1.NIN_GameProjection
