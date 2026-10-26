import CPS_BoundaryLoad
import CPS_Ordinary
import CPS_ParentStatus
import CPR_DataPersistence
import CPR_SourceBank
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPG_Projection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open Hist_Store Hist_RuntimeEntry CPP_BankState MultiproofConeCanonical
open AspisV8R19.DuplexFrames
attribute [local instance] Classical.propDecidable

/-- Data-only transaction observations in one GLOBAL bank-key namespace.
`actions` is the ordered physical projection after the checkpoint copy, up to
parent completion. The native copy itself is recorded by `copied`.
No source acceptance, history, persistence, or security proposition is a field.
The projection's source action semantics are the existing CPP bank semantics;
this is a checkpoint projection, not a model of the entire validator. -/
structure Observations (Tx A : Type) where
  bank : Tx → Bank
  layout : Tx → Layout
  next : Tx → Tx → Prop
  intervening : Tx → Tx → List Nat
  parentReply : Tx → CPP_Atomic.Reply Unit
  copied : Tx → alloc.vec.Vec U8
  actions : Tx → List (Action A)

/-- At a transaction boundary a zero-funded account has no loaded bytes.
Normalize only this data projection, preserving owner and balance. -/
def cached (bank : Bank) : Bank :=
  ⟨fun key => ⟨(bank.cells key).owner,
    if bank.lamports key = 0 then ⟨[],by simp⟩ else (bank.cells key).data⟩,
   bank.lamports⟩

def entry {Tx A : Type} (p : Observations Tx A) (t : Tx) : Entry :=
  Hist_RuntimeEntry.load (cached (p.bank t)).cells
    (CPP_BankState.layout (cached (p.bank t)) (p.layout t))

def before {Tx A : Type} (p : Observations Tx A) (t : Tx) (key : Nat) : CPR_DataPersistence.Image :=
  CPR_DataPersistence.snapshot (p.bank t) key

def loaded {Tx A : Type} (p : Observations Tx A) (t : Tx) (key : Nat) : Option Bytes :=
  CPR_DataPersistence.visible (before p t key)

def success {Tx A : Type} (p : Observations Tx A) (t : Tx) : Bool :=
  CPS_ParentStatus.success (p.parentReply t)

/-- Conservative ordinary-account domain: exclude ALL signing accounts and ALL
system-owned accounts. The runtime fee payer is signing and a durable nonce is
system-owned, so this is a restriction of the approved ordinary domain, not an
extension of the persistence law to exceptional accounts. The non-system
verifier program pin remains explicit in the source theorem. -/
def ordinary {Tx A : Type} (p : Observations Tx A)
    (system : S2W_ExtractionBoundary.Program) (t : Tx) (key : Nat) : Prop :=
  ((entry p t).records key).owned.is_signer = false ∧
  ((entry p t).records key).owned.owner ≠ system

def adjacent {Tx A : Type} (p : Observations Tx A) (t u : Tx) : Prop :=
  p.next t u ∧ ((p.layout t).handles 2).1 ∉ p.intervening t u

variable {Tx A : Type} (p : Observations Tx A)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def result (t : Tx) : Bank × List S2X.AccountEvent :=
  CPP_BankHistory.run n1 n2 copy allocator id
    (CPR_SourceBank.afterCopy (cached (p.bank t)) ((p.layout t).handles 2).1 (p.copied t))
    (p.actions t)

def tentative (t : Tx) (key : Nat) : CPR_DataPersistence.Image :=
  CPR_DataPersistence.snapshot (result p n1 n2 copy allocator id t).1 key

theorem dead (t : Tx) (key : Nat) (zero : (p.bank t).lamports key = 0) :
    ((entry p t).buffers key).val = [] := by
  change ((if (p.bank t).lamports key = 0 then (⟨[],by simp⟩ : Slice U8) else ((p.bank t).cells key).data)).val = []
  rw [if_pos zero]

theorem live (t : Tx) (key : Nat) (positive : 0 < (p.bank t).lamports key) :
    loaded p t key = some (bytesOf ((entry p t).buffers key).val) := by
  change (if (p.bank t).lamports key = 0 then none else _) =
    some (bytesOf (if (p.bank t).lamports key = 0 then (⟨[],by simp⟩ : Slice U8) else ((p.bank t).cells key).data).val)
  rw [if_neg (by omega),if_neg (by omega)]

#print axioms dead
#print axioms live
end AspisR1.CPG_Projection
end
