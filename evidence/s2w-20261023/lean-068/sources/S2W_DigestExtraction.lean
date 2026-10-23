import S2W_TwoFieldAudit

/-! The exact already emitted three-line SolanaDigest wrapper and to_bytes
body, with only the opaque hashv callee parameterized. The current production
method is byte-identical to the retained extracted source fragment. See
S2W_digest_inventory.py and digest-source-reuse.json; no S4 candidate edited.
This does not reattribute the old cone theorem or assume NativeBinding. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_DigestExtraction
open Aeneas Aeneas.Std Result
open S2W_ExtractionBoundary
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Parts := S2Z.Oracle.Parts
abbrev Digest := S2Z.Oracle.Digest

/-- Exact emitted Hash::to_bytes body; Hash is emitted as Array U8 32. -/
def toBytes (self : Digest) : Result Digest := do
  ok self

/-- Exact emitted source digest body after the recorded single external-callee
substitution and nominal carrier reuse. Neither success nor totality assumed. -/
def digest (hashv : Parts → Result Digest) (self : AdapterRw.SolanaDigest)
    (parts : Parts) : Result Digest := do
  let h ← hashv parts
  toBytes h

/-- Source wrapper contributes no extra value or termination premise. -/
theorem digest_eq_hashv (hashv : Parts → Result Digest) (self : AdapterRw.SolanaDigest)
    (parts : Parts) : digest hashv self parts = hashv parts := by
  unfold digest toBytes
  cases hashv parts <;> rfl

/-- D188 extraction trust refers to the EXTRACTED source wrapper here, rather
than treating its old opaque op43 as already proved to be hashv. These are
source-function interpretation equalities, not any caller field or conclusion.
The code identity/reused emission audit is explicit in the evidence packet. -/
structure AeneasExtraction (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : Parts → Result Digest) : Prop where
  stage1 : ∀ program accounts data,
    native1 program accounts data = AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data
  stage2 : ∀ program accounts data slot,
    native2 program accounts data slot = AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts data slot
  digestSource : ∀ self parts, ops.op43 self parts = digest hashv self parts

/-- NativeBinding is now a theorem from the source wrapper extraction. -/
theorem native_binding (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : Parts → Result Digest) (extraction : AeneasExtraction ops native1 native2 hashv) :
    S2Z.Oracle.NativeBinding ops hashv := by
  intro self parts
  exact (extraction.digestSource self parts).trans (digest_eq_hashv hashv self parts)

/-- Transport into earlier helpers; their digest equality is derived, not a
second trusted premise. All final uses should construct it through this map. -/
def sourceBoundary (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : Parts → Result Digest) (extraction : AeneasExtraction ops native1 native2 hashv) :
    S2W_ExtractionBoundary.AeneasExtraction ops native1 native2 hashv :=
  ⟨extraction.stage1,extraction.stage2,native_binding ops native1 native2 hashv extraction⟩

/-- No extra NativeBinding or total oracle premise at the native source port. -/
theorem native_oracle (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : Parts → Result Digest) (extraction : AeneasExtraction ops native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (runtime : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    CheckpointBytes5Inputs.Oracle (S2Z.Oracle.leadDigest ops) () H :=
  S2W_ExtractionBoundary.native_oracle ops native1 native2 hashv
    (sourceBoundary ops native1 native2 hashv extraction) sha256 H p1 runtime

#print axioms digest_eq_hashv
#print axioms native_binding
#print axioms native_oracle
#print AeneasExtraction
end AspisR1.S2W_DigestExtraction
end
