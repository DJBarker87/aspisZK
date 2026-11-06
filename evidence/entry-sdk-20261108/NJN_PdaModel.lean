import NJH_SyscallLaws
set_option autoImplicit false
namespace NJN_PdaModel
inductive Reply where
  | ok (bytes : List Nat)
  | maxSeedLengthExceeded
  | invalidSeeds
  | illegalOwner
  | abort
  deriving DecidableEq
structure Input where
  seeds : List (List Nat)
  programId : List Nat
  deriving DecidableEq

def forward (status : Nat) (output : List Nat) : Reply :=
  if status = 0 then .ok output else if status = 1 then .invalidSeeds
  else if status = 2 then .illegalOwner else .abort

def validSeeds (input : Input) : Prop := input.seeds.length ≤ 16 ∧ ∀ s ∈ input.seeds, s.length ≤ 32
instance (input : Input) : Decidable (validSeeds input) := by unfold validSeeds; infer_instance
structure Output (Frame : Type) where
  input : Input
  region : List Nat
  called : Bool
  status : Nat
  reply : Reply
  frame : Frame

def invoke {Frame : Type} (frame : Frame) (input : Input) (status : Nat) (region : List Nat) : Output Frame :=
  if validSeeds input then ⟨input,region,true,status,forward status region,frame⟩
  else ⟨input,region,false,status,.maxSeedLengthExceeded,frame⟩

theorem ok (bytes : List Nat) : forward 0 bytes = .ok bytes := by simp [forward]
theorem invalid (bytes : List Nat) : forward 1 bytes = .invalidSeeds := by simp [forward]
theorem illegal (bytes : List Nat) : forward 2 bytes = .illegalOwner := by simp [forward]
theorem unsupported (bytes : List Nat) (status : Nat) (h : 2 < status) :
    forward status bytes = .abort := by
  have h0 : status ≠ 0 := by omega
  have h1 : status ≠ 1 := by omega
  have h2 : status ≠ 2 := by omega
  simp [forward,h0,h1,h2]
/-- Invalid seed prefix returns without a runtime call. -/
theorem rejected {F : Type} (f : F) (input : Input) (s : Nat) (b : List Nat)
    (bad : ¬ validSeeds input) :
    (invoke f input s b).called = false ∧
    (invoke f input s b).reply = .maxSeedLengthExceeded := by simp [invoke,bad]
/-- Ordered nested seed lists and the program id are retained verbatim; no PDA value law. -/
theorem arguments_frame {F : Type} (f : F) (input : Input) (s : Nat) (b : List Nat) :
    (invoke f input s b).input = input ∧ (invoke f input s b).region = b ∧
    (invoke f input s b).status = s ∧ (invoke f input s b).frame = f := by
  unfold invoke
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩
#print axioms ok
#print axioms invalid
#print axioms illegal
#print axioms unsupported
#print axioms rejected
#print axioms arguments_frame
end NJN_PdaModel
