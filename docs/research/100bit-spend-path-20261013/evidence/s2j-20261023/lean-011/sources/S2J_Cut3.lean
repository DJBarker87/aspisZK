import S2J_Cut2

set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2J
open S2Trust S2H S2E_Reference.S2E_Reference

/-- A local shared account reference, NOT an Rc clone or data guard. -/
structure PublicSelectionRelated {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (observe : W → NativeArguments)
    (fixed : FixedInvocation) (o : Originals W Child Alloc Event)
    (n : (W × Option AccountReference) × Option AccountReference) (r : (OwnedCut Child Alloc Event × Option OwnedAccount) × Option OwnedAccount) : Prop where
  proof : SelectionRelated L observe fixed o n.1 r.1
  referenceBound : match n.2,r.2 with
    | none,none => True
    | some a,some b => a.record = b ∧ a.handle = o.allocations.handle 1
    | _,_ => False

/-- Native slice indexing's TrustedStd value/identity interpretation. The handle
identifies the selected record, not a fresh allocation or an SDK data borrow. -/
def nativeSelect1 {W : Type} (observe : W → NativeArguments) (_ : S2F.Step)
    (n : (W × Option AccountReference) × Option AccountReference) :
    S2F.Outcome solana_program_error.ProgramError ((W × Option AccountReference) × Option AccountReference) :=
  match (observe n.1.1).accounts.val[1]? with
  | none => .abort n
  | some a => .next (n.1,some ⟨(observe n.1.1).accountHandle 1,a⟩)

/-- This is the exact second index call at the start of extracted admission. -/
def referenceSelect1 {Child Alloc Event : Type} (_ : S2F.Step)
    (r : (OwnedCut Child Alloc Event × Option OwnedAccount) × Option OwnedAccount) :
    S2F.Outcome solana_program_error.ProgramError ((OwnedCut Child Alloc Event × Option OwnedAccount) × Option OwnedAccount) :=
  match alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      r.1.1.sdk.accounts 1#usize with
  | .ok a => .next (r.1,some a)
  | .fail _ => .abort r
  | .div => .abort r

/-- Cut3 selection preserves the full invocation and heap relation and installs
an associated local reference; no borrow counter, ownership or byte is changed. -/
theorem cut3_stepLaw {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (observe : W → NativeArguments)
    (fixed : FixedInvocation) (o : Originals W Child Alloc Event) :
    S2F.StepLaw (PublicSelectionRelated L observe fixed) (nativeSelect1 observe)
      referenceSelect1 o .accounts := by
  intro n r related
  have inv := related.proof.invocation
  unfold nativeSelect1 referenceSelect1
  have indexEq : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      r.1.1.sdk.accounts 1#usize =
      (match r.1.1.sdk.accounts.val[1]? with
       | none => fail .arrayOutOfBounds
       | some a => ok a) := by
    rw [alloc.vec.Vec.index_slice_index]
    cases h : r.1.1.sdk.accounts.val[1]? <;> simp [alloc.vec.Vec.index_usize,h]
  rw [inv.nativeAccounts,indexEq]
  cases read : r.1.1.sdk.accounts.val[1]? with
  | none => exact .abort related
  | some a =>
    apply S2F.Matches.next
    refine ⟨related.proof,rfl,?_⟩
    apply inv.handles
    apply Nat.lt_of_not_ge
    intro h
    rw [List.getElem?_eq_none h] at read
    cases read

#print axioms cut3_stepLaw
end AspisR1.S2J
