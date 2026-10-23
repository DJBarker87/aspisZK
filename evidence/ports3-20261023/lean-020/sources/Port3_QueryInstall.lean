import Port3_QueryFrame
import Port3_Constructor

/-! Installs the complete retained source-shaped query loop, not an arbitrary
successful query return. Leaf opening/arithmetic interpretations remain named
owner obligations. This installation alone does not assert a frozen-model port. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_QueryInstall
open Aeneas Aeneas.Std Result

 def phase : AspisR1Stage2.verifier.Phase → VTop_Stages.verifier.Phase
  | .Parsed => .Parsed | .Semantic => .Semantic | .SemanticPart p => .SemanticPart p
  | .Prepare => .Prepare | .CheckpointRead => .CheckpointRead | .Merkle n => .Merkle n
  | .Query n => .Query n | .QueryPart n p => .QueryPart n p
  | .CheckpointWrite => .CheckpointWrite | .Relation => .Relation | .Final => .Final

def observer (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) :
    Option (AspisR1Stage2.verifier.Phase → Result Unit) :=
  obs.map (fun f => fun p => f (phase p))

def result {A : Type} (m : Result (core.result.Result A AspisR1Stage2.verifier.Error)) :
    Result (core.result.Result A VTop_Stages.verifier.Error) := do
  let r ← m
  match r with
  | .Ok a => ok (.Ok a)
  | .Err e => ok (.Err (Port3_CheckpointInstall.error e))

theorem success_iff {A : Type}
    (m : Result (core.result.Result A AspisR1Stage2.verifier.Error)) (a : A) :
    result m = ok (.Ok a) ↔ m = ok (.Ok a) := by
  cases m with
  | fail e => simp [result]
  | div => simp [result]
  | ok r => cases r <;> simp [result]

def query (aops : AspisR1Stage2.AccumulateOps) (qops : AspisR1Stage2.QueryOps)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (g : Array VTop_Stages.aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (geometry : VTop_Stages.verifier.QueryGeometry) (pending : VTop_Stages.verifier.BatchedWeights)
    (end1 : Usize) :=
  result (AspisR1Stage2.verifier.candidate.query_loop
    (AspisR1Stage2.verifier.candidate.queryWithOps aops qops)
    proof p a g (observer obs) geometry pending end1)

def install (base : VTop_Stages.Ops) (reserved : Bool)
    (aops : AspisR1Stage2.AccumulateOps) (qops : AspisR1Stage2.QueryOps) : VTop_Stages.Ops :=
  {Port3_Constructor.installed base reserved with op6 := query aops qops, op16 := ok 10#usize}

theorem returned_fields (aops : AspisR1Stage2.AccumulateOps) (qops : AspisR1Stage2.QueryOps)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
    (a out : VTop_Stages.verifier.Accumulator)
    (g : Array VTop_Stages.aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (geometry : VTop_Stages.verifier.QueryGeometry)
    (pending after : VTop_Stages.verifier.BatchedWeights) (end1 : Usize)
    (bound : a.next.val ≤ end1.val)
    (success : query aops qops proof p a g obs geometry pending end1 = ok (.Ok (out,after))) :
    out.weights = a.weights ∧ out.next.val = end1.val :=
  Port3_QueryFrame.loop_fields aops qops proof p a out g (observer obs) geometry pending after
    end1 bound ((success_iff _ _).mp success)

/-- Derived from the SAME actual prefix's op12 and op6 cuts. The post-flush
Vec still needs its own length/canonicality theorem; it is not guessed here. -/
theorem writer_query_fields (base : VTop_Stages.Ops) (reserved : Bool)
    (aops : AspisR1Stage2.AccumulateOps) (qops : AspisR1Stage2.QueryOps)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize)
    (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (prefix : VTop_Provenance.WriterPrefix (install base reserved aops qops)
      D hash semantic proof split none p a) :
    split.val = 10 ∧ a.next.val = 10 ∧
      ∃ (returned : VTop_Stages.verifier.Accumulator)
        (pending : VTop_Stages.verifier.BatchedWeights)
        (flushed : Slice VTop_Stages.aspis_core.field.QM31),
        returned.weights.val = List.replicate 64 Port2_Initial.zeroK ∧
        (install base reserved aops qops).op9 pending returned.weights.deref = ok flushed ∧
        a.weights.val = flushed.val := by
  obtain ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
    hw,hr,hp,hn⟩ := prefix
  have hsplit : split.val = 10 := by
    have e : (10#usize : Usize) = sv := Result.ok.inj hs
    subst sv
    exact hsv
  have hi : Port3_Initial.constructor reserved .S2 = ok (.Ok initial) := by
    change Port3_Constructor.extracted (Port3_Constructor.leaves reserved) .S2 = _ at hinit
    rw [Port3_Constructor.normalization] at hinit
    exact hinit
  have fields := Port3_Initial.accepted_fields base reserved initial hi
  have frame := returned_fields aops qops proof p initial returned.1 g none geometry pending returned.2 split
    (by rw [fields.2.2.2.2]; simp) hquery
  refine ⟨hsplit,?_,returned.1,returned.2,flushed,?_,hflush,hw⟩
  · rw [hn,frame.2,hsplit]
  · rw [frame.1,fields.2.1]

#print axioms success_iff
#print axioms returned_fields
#print axioms writer_query_fields
end AspisR1.Port3_QueryInstall
end
