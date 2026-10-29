import R1Z.PV_RunJoin_ActualRunSources59
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualPlanSources59
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PublishSkeleton54
open PV_RunJoin_NativeControl55 (Phase)
variable [ExternalTypes] [ExternalFuns]

def empty : alloc.vec.Vec U8 := ⟨[],by simp⟩

def publicationBytes (p : Phase) (f : prover.Publication → Result (alloc.vec.Vec U8)) : Bytes :=
  match PV_RunJoin_ActualRunSources59.finish p with
  | .ok (.Ok publication) =>
    match f publication with
    | .ok out => bytes out.val
    | _ => []
  | _ => []

def compactSemantic (p : prover.Publication) : Result (alloc.vec.Vec U8) := do
  let (status,out) ← host_compact.compact_semantic (alloc.vec.Vec.deref p.semantic_bytes) empty
  match status with
  | .Ok _ => ok out
  | .Err _ => ok empty

def compactClaim (p : prover.Publication) : Result (alloc.vec.Vec U8) := do
  let (status,out) ← host_compact.compact_values (alloc.vec.Vec.deref p.y1) empty
  match status with
  | .Ok _ => ok out
  | .Err _ => ok empty

/-- One literal emitted query-body call, starting from an empty prefix. No
successful full serializer output is used to define any model byte. -/
def queryBytes (p : prover.Publication) (i : Usize) : Result (alloc.vec.Vec U8) := do
  let cc1 ← core.option.Option.unwrap p.backend.c1
  let cc2 ← core.option.Option.unwrap p.backend.c2
  let step ← prover.append_query_openings_loop.body cc1 cc2 p.queries
    (alloc.vec.Vec.deref p.folded_word) p.folded_salts empty i
  match step with
  | .cont (out,_) => ok out
  | .done out => ok out

/-- The six slices are the actual compact format's 480/128/32/32/128/32
query fields. Slicing remains symbolic. -/
def queryPart (p : Phase) (i : Fin 22) : ProverCommitPublish43.QueryParts :=
  let payload := publicationBytes p (fun publication => queryBytes publication (UScalar.ofNatCore i.val (by rw [UScalarTy.Usize_numBits_eq]; omega)))
  ⟨payload.take 480,(payload.drop 480).take 128,(payload.drop 608).take 32,
    (payload.drop 640).take 32,(payload.drop 672).take 128,(payload.drop 800).take 32⟩

def nodeBytes (p : prover.Publication) (batch t : Usize) :
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
  let cc1 ← core.option.Option.unwrap p.backend.c1
  let cc2 ← core.option.Option.unwrap p.backend.c2
  let idx ← prover.publication_indices p.queries (if batch=0#usize then 0#usize else compact.SPLIT)
    (if batch=0#usize then compact.SPLIT else 22#usize) (t=2#usize)
  let nodes ← match t.val with
    | 0 => host_commitment.Commitment.multiproof cc1 (alloc.vec.Vec.deref idx)
    | 1 => host_commitment.Commitment.multiproof cc2 (alloc.vec.Vec.deref idx)
    | _ => host_tree.BinaryTree.multiproof p.tree (alloc.vec.Vec.deref idx)
  core.option.Option.ok_or nodes verifier.Error.Allocation

def slot (p : Phase) (i : Fin 6) : ProverCommitPublish43.Slot :=
  let nodes := match PV_RunJoin_ActualRunSources59.finish p with
    | .ok (.Ok publication) =>
      match nodeBytes publication (UScalar.ofNatCore (i.val/3) (by rw [UScalarTy.Usize_numBits_eq]; omega))
          (UScalar.ofNatCore (i.val%3) (by rw [UScalarTy.Usize_numBits_eq]; omega)) with
      | .ok (.Ok out) => Except.ok (bytes out.val)
      | _ => Except.error ProverCommitPublish43.Error.merkle
    | _ => Except.error ProverCommitPublish43.Error.merkle
  ⟨nodes,32*([146,146,128,172,172,150][i.val]?.getD 0)⟩

def header : Bytes := bytes [82#u8,49#u8,80#u8,51#u8,67#u8,66#u8,49#u8,56#u8] ++
  bytes [2#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

#print axioms empty
#print axioms publicationBytes
#print axioms compactSemantic
#print axioms compactClaim
#print axioms queryBytes
#print axioms queryPart
#print axioms nodeBytes
#print axioms slot
#print axioms header
end R1Z.PV_RunJoin_ActualPlanSources59
