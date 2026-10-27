import AspisR1CircleCaller25.Funs
import R1Z.ProverCommitCircleSampler22
import R1Z.ProverCommitSemantic20
/-! Concrete circle policy and extracted caller success/state transport.
These nominal maps retain every machine coefficient; the generic policy is
instantiated with the existing unconditional sampler, including fallbacks. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCircle25
open Aeneas Aeneas.Std Result AspisR1CircleCaller25
abbrev Q := aspis_core.field.QM31
abbrev WQ := AspisR1CircleSampleWrapper.field.QM31
abbrev Bytes32 := Array U8 32#usize
abbrev State (H : Type) := r1_wire.SemanticTranscript H

def fromWrapper (q : WQ) : Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toWrapper (q : Q) : WQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem wrapper_roundtrip (q : WQ) : toWrapper (fromWrapper q) = q := by cases q; rfl

def fromSemantic {H : Type} (s : ProverCommitSemantic20.State H) : State H :=
  ⟨s.state,s.hash,s.next_row⟩
def toSemantic {H : Type} (s : State H) : ProverCommitSemantic20.State H :=
  ⟨s.state,s.hash,s.next_row⟩

theorem semantic_roundtrip {H : Type} (s : ProverCommitSemantic20.State H) :
    toSemantic (fromSemantic s) = s := by cases s; rfl

def fromHash {H : Type} (hash : AspisR1SimSemantic20.aspis_core.digest.Digest32 H) :
    aspis_core.digest.Digest32 H := ⟨hash.coremarkerCopyInst,hash.digest⟩

def fromError : AspisR1SimSemantic20.r1_wire.Error → r1_wire.Error
  | .Allocation => .Allocation
  | .RowOrder expected actual => .RowOrder expected actual
  | .InvalidRow => .InvalidRow
  | .Tag row => .Tag row
  | .Length row => .Length row
  | .NonCanonical row index => .NonCanonical row index
  | .Boundary round => .Boundary round
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public
  | .ActivePole => .ActivePole

def fromBlock {H : Type} (value : (core.result.Result Bytes32
    AspisR1SimSemantic20.r1_wire.Error) × ProverCommitSemantic20.State H) :
    (core.result.Result Bytes32 r1_wire.Error) × State H :=
  ((match value.1 with
    | core.result.Result.Ok block => core.result.Result.Ok block
    | core.result.Result.Err error => core.result.Result.Err (fromError error)),fromSemantic value.2)

/-- Universal nominal transport of the actual three-read block method,
including every hash failure/divergence and the row-order rejection state. -/
theorem block_transport {H : Type} (hash : AspisR1SimSemantic20.aspis_core.digest.Digest32 H)
    (state : ProverCommitSemantic20.State H) (row : U8) (record : Slice U8) :
    (do let value ← AspisR1SimSemantic20.r1_wire.SemanticTranscript.sample_block_validated
          hash state row record
        ok (fromBlock value)) =
      r1_wire.SemanticTranscript.sample_block_validated (fromHash hash)
        (fromSemantic state) row record := by
  simp only [AspisR1SimSemantic20.r1_wire.SemanticTranscript.sample_block_validated,
    r1_wire.SemanticTranscript.sample_block_validated,fromHash,fromSemantic,lift,bind_tc_ok]
  split
  · rfl
  · simp only [bind_assoc,bind_tc_ok]
    rfl

def row (second : Bool) : AspisR1CircleSampleWrapper.r0_transcript.CircleRow :=
  if second then .Second else .First

def points (p : AspisR1CircleSampleWrapper.circle.SecureCirclePoint) : Array Q 2#usize :=
  Array.make 2#usize [fromWrapper p.x,fromWrapper p.y]

def decodeQ (q : Q) : AspisWideTower.WideExact :=
  (ProverCommitCircleSampler22.coordinates ⟨toWrapper q,toWrapper q⟩).1

def decode (q : Array Q 2#usize) : List AspisWideTower.WideExact := q.val.map decodeQ

def sample (block : Bytes32) (second : Bool) : Result (Array Q 2#usize) := do
  let p ← AspisR1CircleSampleWrapper.sampler.circle_sample block (row second)
  ok (points p)

def policy : r1_wire.circle25.Policy Unit where point := sample

theorem points_decode (p : AspisR1CircleSampleWrapper.circle.SecureCirclePoint) :
    decode (points p) = [ (ProverCommitCircleSampler22.coordinates p).1,
      (ProverCommitCircleSampler22.coordinates p).2 ] := by
  simp only [decode,points,Array.make,List.map_cons,List.map_nil,decodeQ,wrapper_roundtrip]
  rfl

/-- Both circle rows are total with exact model coordinates on all blocks,
including singular/subfield fallbacks. No sampler-policy parameter remains. -/
theorem sample_total (block : Bytes32) (second : Bool) :
    ∃ value, policy.point block second = ok value ∧
      decode value = [ (ProverCommitCircleSampler22.model block (row second)).1.1,
        (ProverCommitCircleSampler22.model block (row second)).1.2 ] := by
  obtain ⟨p,h,meaning⟩ := ProverCommitCircleSampler22.circle_total_coordinates block (row second)
  refine ⟨points p,?_,?_⟩
  · simp only [policy,sample,h,bind_tc_ok]
  · rw [points_decode,meaning]

/-- The extracted first-circle caller consumes exactly the sampled block,
returns the installed point and retains the entire advanced state. -/
theorem first_caller {H : Type} (hash : aspis_core.digest.Digest32 H)
    (state next : State H) (record : alloc.vec.Vec U8) (block : Bytes32)
    (order : state.next_row = 25#u8)
    (checked : r1_wire.semantic20.checked 25#u8 (alloc.vec.Vec.deref record) =
      ok (core.result.Result.Ok ()))
    (sampled : r1_wire.SemanticTranscript.sample_block_validated hash state 25#u8
      (alloc.vec.Vec.deref record) = ok (core.result.Result.Ok block,next)) :
    ∃ value, decode value = [ (ProverCommitCircleSampler22.model block .First).1.1,
        (ProverCommitCircleSampler22.model block .First).1.2 ] ∧
      r1_wire.circle25.point hash policy state 25#u8 record =
        ok (core.result.Result.Ok value,next) := by
  obtain ⟨value,h,meaning⟩ := sample_total block false
  refine ⟨value,meaning,?_⟩
  simp [r1_wire.circle25.point,order,checked,sampled,h]
  rfl

/-- The second row has its distinct fallback and retains its own advanced
state, rather than reusing the first row's value or state. -/
theorem second_caller {H : Type} (hash : aspis_core.digest.Digest32 H)
    (state next : State H) (record : alloc.vec.Vec U8) (block : Bytes32)
    (order : state.next_row = 26#u8)
    (checked : r1_wire.semantic20.checked 26#u8 (alloc.vec.Vec.deref record) =
      ok (core.result.Result.Ok ()))
    (sampled : r1_wire.SemanticTranscript.sample_block_validated hash state 26#u8
      (alloc.vec.Vec.deref record) = ok (core.result.Result.Ok block,next)) :
    ∃ value, decode value = [ (ProverCommitCircleSampler22.model block .Second).1.1,
        (ProverCommitCircleSampler22.model block .Second).1.2 ] ∧
      r1_wire.circle25.point hash policy state 26#u8 record =
        ok (core.result.Result.Ok value,next) := by
  obtain ⟨value,h,meaning⟩ := sample_total block true
  refine ⟨value,meaning,?_⟩
  simp [r1_wire.circle25.point,order,checked,sampled,h]
  rfl

#print axioms block_transport
#print axioms wrapper_roundtrip
#print axioms semantic_roundtrip
#print axioms points_decode
#print axioms sample_total
#print axioms first_caller
#print axioms second_caller
end R1Z.ProverCommitCircle25
