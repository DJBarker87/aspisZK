import S2H_CutRelation

set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2J
open S2Trust S2H S2E_Reference.S2E_Reference

/-- Observations of actual entrypoint arguments. Descriptor identities are
runtime allocation identities, not hashes or integer equality substitutes. -/
structure NativeArguments where
  instruction : Slice U8
  instructionDescriptor : Descriptor
  program : Array U8 32#usize
  accounts : alloc.vec.Vec OwnedAccount
  accountsDescriptor : Descriptor
  accountHandle : Nat → Nat
  accountCount : Usize

/-- A fixed invocation before execution, including both slice descriptors. -/
structure FixedInvocation where
  arguments : NativeArguments

/-- The exact missing runtime/source premise: entrypoint deserialization exposes
these original argument records in order, their slice lengths and allocation
association. P2/P2'/P3/P4 do not themselves state this theorem. No native
acceptance, successful child, caller output or oracle equality occurs here. -/
structure EntrypointDeserialization {W Child Alloc Event : Type}
    (observe : W → NativeArguments) (o : Originals W Child Alloc Event)
    (fixed : FixedInvocation) : Prop where
  atEntry : observe o.native = fixed.arguments
  instruction : fixed.arguments.instruction = o.input.data
  instructionLength : fixed.arguments.instructionDescriptor.length = o.input.data.val.length
  program : fixed.arguments.program = o.input.program
  accounts : fixed.arguments.accounts = o.input.sdk.accounts
  accountsLength : fixed.arguments.accountsDescriptor.length = o.input.sdk.accounts.val.length
  count : fixed.arguments.accountCount = alloc.vec.Vec.len o.input.sdk.accounts
  handles : ∀ i, i < o.input.sdk.accounts.val.length →
    fixed.arguments.accountHandle i = o.allocations.handle i

/-- Extension, leaving every inherited full heap/token obligation intact. The
original instruction and descriptor stay fixed at subsequent caller cuts. -/
structure InvocationRelated {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (observe : W → NativeArguments)
    (fixed : FixedInvocation) (o : Originals W Child Alloc Event)
    (native : W) (owned : OwnedCut Child Alloc Event) : Prop extends CutRelated L o native owned where
  arguments : observe native = fixed.arguments
  nativeInstruction : (observe native).instruction = owned.instruction
  instructionLength : (observe native).instructionDescriptor.length = owned.instruction.val.length
  nativeProgram : (observe native).program = owned.program
  nativeAccounts : (observe native).accounts = owned.sdk.accounts
  accountsLength : (observe native).accountsDescriptor.length = owned.sdk.accounts.val.length
  count : (observe native).accountCount = alloc.vec.Vec.len owned.sdk.accounts
  handles : ∀ i, i < owned.sdk.accounts.val.length →
    (observe native).accountHandle i = o.allocations.handle i

def initialCut {W Child Alloc Event : Type} (o : Originals W Child Alloc Event) :
    OwnedCut Child Alloc Event :=
  ⟨o.input.sdk,o.input.state,o.heap,[],o.input.program,o.input.data⟩

/-- Initial relatedness from fixed runtime admission and explicit deserialization,
without using any later acceptance observation. -/
theorem invocation_from_runtime {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (observe : W → NativeArguments)
    (fixed : FixedInvocation) (o : Originals W Child Alloc Event)
    (admitted : Admitted L o)
    (deserialized : EntrypointDeserialization observe o fixed) :
    InvocationRelated L observe fixed o o.native (initialCut o) := by
  refine ⟨⟨admitted.nativeHeap,admitted.valid,admitted.image,admitted.ambient,
    rfl,rfl,?_⟩,deserialized.atEntry,?_,?_,?_,?_,?_,?_,?_⟩
  · intro b member
    cases member
  all_goals rw [deserialized.atEntry]
  · exact deserialized.instruction
  · exact deserialized.instructionLength
  · exact deserialized.program
  · exact deserialized.accounts
  · exact deserialized.accountsLength
  · exact deserialized.count
  · exact deserialized.handles

#print axioms invocation_from_runtime
end AspisR1.S2J
