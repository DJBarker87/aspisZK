import R1Z.ProverCommitCompactRows46
/-! Ordered native proof front and final byte assembly. All codec errors
precede query/node publication; both fixed byte-length guards are retained. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFront46
open Aeneas.Std Result
open ProverCommitPublish43 (Bytes)
open ProverCommitCompactSource46 ProverCommitCompactRows46
attribute [local instance] Classical.propDecidable
abbrev Error := ProverCommitPublish43.Error

def header : Bytes := [82,49,80,51,67,66,49,56,2,0,0,0,0,0,0,0]
structure Fields where
  logical : Bytes
  y1 : Bytes
  inactive : Bytes
  c0 : Bytes
  foldedRoot : Bytes
  c1 : Bytes
  fin : Bytes

def suffix (f : Fields) := f.inactive ++ f.c0 ++ f.foldedRoot ++ f.c1 ++ f.fin

def sourceFront (api : API) (f : Fields) : Result (Except Error Bytes) := do
  let first ← sourceCompact api f.logical header
  match first with
  | .error e => ok (.error e)
  | .ok out =>
    match sourceValues api f.y1 out with
    | .error e => ok (.error e)
    | .ok out => ok (.ok (out ++ suffix f))

def referenceFront (f : Fields) : Except Error Bytes :=
  (referenceCompact f.logical header).bind (fun out =>
    (referenceValues f.y1 out).bind (fun out => .ok (out ++ suffix f)))

theorem front_source (api : API) (std : TrustedChunks api) (f : Fields) :
    sourceFront api f = ok (referenceFront f) := by
  rw [sourceFront,compact_source api std]
  simp only [bind_tc_ok,values_source api std,referenceFront]
  cases referenceCompact f.logical header with
  | error e => rfl
  | ok out =>
    simp only [Except.bind]
    cases referenceValues f.y1 out <;> rfl

def sourceProof (api : API) (f : Fields) (queries : List ProverCommitPublish43.QueryParts)
    (slots : List ProverCommitPublish43.Slot) : Result (Except Error Bytes) := do
  let front ← sourceFront api f
  ok (ProverCommitPublish43.assembleLoop front queries slots 28359 57607)

def referenceProof (f : Fields) (queries : List ProverCommitPublish43.QueryParts)
    (slots : List ProverCommitPublish43.Slot) : Except Error Bytes :=
  ProverCommitPublish43.assemble (referenceFront f) queries slots 28359 57607

/-- The header, compact semantic/y1 bytes, suffix, repeated query payloads,
node slots, and both length guards occur in the shipped order. Node-call
errors remain explicit Slot results until the native multiproof is installed. -/
theorem proof_source (api : API) (std : TrustedChunks api) (f : Fields)
    (queries : List ProverCommitPublish43.QueryParts) (slots : List ProverCommitPublish43.Slot) :
    sourceProof api f queries slots = ok (referenceProof f queries slots) := by
  rw [sourceProof,front_source api std]
  simp only [bind_tc_ok,referenceProof,ProverCommitPublish43.assemble_loop]

#print axioms front_source
#print axioms proof_source
end R1Z.ProverCommitFront46
