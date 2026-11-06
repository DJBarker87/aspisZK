import NJC_OrderedCalls
set_option autoImplicit false
noncomputable section
namespace NJJ_Cuts
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev Row := Port3_NativePendingBody.Row
abbrev K := aspis_core.field.QM31

/-- Exact logical payload/frame transcription of pending_step. The native
harness also asserts SAME raw/weights allocation IDs and capacities, recorded
in NJJ_CERTIFICATES.md; those are machine ownership facts under (y)/D188,
not new hypotheses about arbitrary model vectors. Every cell is quantified. -/
def pendingStep (weights : Slice K) (before after : alloc.vec.Vec Row)
 (i next : Nat) : Prop :=
 next=i+1 ∧ after.val.length=64 ∧
 ∀ j, j<64 → after.val[j]?=
  if i=j then (weights.val[i]?).map Port3_PendingInstall.row else before.val[j]?

/-- Extensional consequence of the arbitrary observation index; no
address-implies-payload implication or unobserved-field premise. -/
theorem pending_payload (weights : Slice K) (before after : alloc.vec.Vec Row)
 (i next : Nat) (w : K) (read : weights.val[i]?=some w)
 (size : before.val.length=64) (inside : i<64)
 (cut : pendingStep weights before after i next) :
 after.val=before.val.set i (Port3_PendingInstall.row w) := by
 apply List.ext_getElem?
 intro j
 by_cases bound : j<64
 · rw [cut.2.2 j bound]
   by_cases same : i=j
   · subst j
     rw [if_pos rfl,read,List.getElem?_set_self (by omega)]
     rfl
   · rw [if_neg same,List.getElem?_set_ne same]
 · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by simpa only [List.length_set,size] using Nat.le_of_not_gt bound)]

/-- The native initializer's complete returning constructor is the precise
emitted/model carrier once the finite loop invariant supplies its cells. -/
def pendingEnd (raw : alloc.vec.Vec Row) (out : verifier.BatchedWeights) : Prop :=
 out.raw.val.length=64 ∧ out.terms=0#usize ∧
 ∀ j, j<64 → out.raw.val[j]?=raw.val[j]?

theorem pending_constructor (raw : alloc.vec.Vec Row) (out : verifier.BatchedWeights)
 (size : raw.val.length=64) (cut : pendingEnd raw out) :
 out=⟨raw,0#usize⟩ := by
 have same : out.raw=raw := by
  apply Subtype.ext
  apply List.ext_getElem?
  intro j
  by_cases inside : j<64
  · exact cut.2.2 j inside
  · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
 cases out
 dsimp only at same cut
 cases same
 cases cut.2.1
 rfl

/-- Each successful slot write changes exactly its selected cell. The
Reader child Result remains the full supplied Result; errors do not advance
parent at or write the slot. The native error prefix drops the owned Vec. -/
def weightStep (before after : List K) (i at nextAt : Nat)
 (reply : core.result.Result (K × Nat) verifier.Error) : Prop :=
 after.length=before.length ∧
 match reply with
 | .Err _ => after=before ∧ nextAt=at
 | .Ok (value,cursor) => after=before.set i value ∧ nextAt=cursor

#print axioms pending_payload
#print axioms pending_constructor
end NJJ_Cuts
