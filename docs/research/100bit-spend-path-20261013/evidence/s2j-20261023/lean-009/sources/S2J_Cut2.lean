import S2J_Cut1

set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2J
open S2Trust S2H S2E_Reference.S2E_Reference

/-- A local shared account reference, NOT an Rc clone or data guard. -/
structure AccountReference where
  handle : Nat
  record : OwnedAccount

structure SelectionRelated {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (observe : W → NativeArguments)
    (fixed : FixedInvocation) (o : Originals W Child Alloc Event)
    (n : W × Option AccountReference) (r : OwnedCut Child Alloc Event × Option OwnedAccount) : Prop where
  invocation : InvocationRelated L observe fixed o n.1 r.1
  referenceBound : match n.2,r.2 with
    | none,none => True
    | some a,some b => a.record = b ∧ a.handle = o.allocations.handle 0
    | _,_ => False

/-- Native slice indexing's TrustedStd value/identity interpretation. The handle
identifies the selected record, not a fresh allocation or an SDK data borrow. -/
def nativeSelect0 {W : Type} (observe : W → NativeArguments) (_ : S2F.Step)
    (n : W × Option AccountReference) :
    S2F.Outcome solana_program_error.ProgramError (W × Option AccountReference) :=
  match (observe n.1).accounts.val[0]? with
  | none => .abort n
  | some a => .next (n.1,some ⟨(observe n.1).accountHandle 0,a⟩)

/-- This is the exact first index call at the start of extracted admission. -/
def referenceSelect0 {Child Alloc Event : Type} (_ : S2F.Step)
    (r : OwnedCut Child Alloc Event × Option OwnedAccount) :
    S2F.Outcome solana_program_error.ProgramError (OwnedCut Child Alloc Event × Option OwnedAccount) :=
  match alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      r.1.sdk.accounts 0#usize with
  | .ok a => .next (r.1,some a)
  | .fail _ => .abort r
  | .div => .abort r

/-- Cut2 selection preserves the full invocation and heap relation and installs
an associated local reference; no borrow counter, ownership or byte is changed. -/
set_option pp.all true in
theorem cut2_stepLaw {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (observe : W → NativeArguments)
    (fixed : FixedInvocation) (o : Originals W Child Alloc Event) :
    S2F.StepLaw (SelectionRelated L observe fixed) (nativeSelect0 observe)
      referenceSelect0 o .accounts := by
  intro n r related
  have inv := related.invocation
  unfold nativeSelect0 referenceSelect0
  have indexEq : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      r.1.sdk.accounts 0#usize =
      (match r.1.sdk.accounts.val[0]? with
       | none => fail .arrayOutOfBounds
       | some a => ok a) := by
    rw [alloc.vec.Vec.index_slice_index]
    simp [alloc.vec.Vec.index_usize]
  rw [inv.nativeAccounts,indexEq]
  cases read : r.1.sdk.accounts.val[0]? with
  | none => exact .abort related
  | some a =>
    apply S2F.Matches.next
    refine ⟨inv,rfl,?_⟩
    apply inv.handles
    exact List.length_pos_of_mem (List.mem_of_getElem? read)

#print axioms cut2_stepLaw
end AspisR1.S2J
