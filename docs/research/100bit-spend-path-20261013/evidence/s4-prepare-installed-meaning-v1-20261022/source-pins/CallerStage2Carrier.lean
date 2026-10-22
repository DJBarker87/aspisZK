import AspisR1CurrentCaller.Types
import Stage2ContinuationTypes
import Stage2ContinuationQueryLoop
import Tx1OpsCut
import Aeneas
set_option autoImplicit false
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
namespace AspisR1S4CallerStage2CarrierV1
abbrev FullWide := AspisR1Stage2.aspis_core.field.wide_exact.WideExact

def cmToStage (x : AspisR1CurrentCaller.aspis_core.field.CM31) : AspisR1Stage2.aspis_core.field.CM31 := ⟨x.a,x.b⟩
def qmToStage (x : AspisR1CurrentCaller.aspis_core.field.QM31) : AspisR1Stage2.aspis_core.field.QM31 :=
  ⟨cmToStage x.c0,cmToStage x.c1⟩
def wideToStage (x : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact) : AspisR1Stage2.aspis_core.field.wide_exact.WideExact :=
  ⟨qmToStage x.c0,qmToStage x.c1⟩
def circleToStage (x : AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint) : AspisR1Stage2.aspis_core.circle.SecureCirclePoint :=
  ⟨qmToStage x.x,qmToStage x.y⟩
def variantToStage (x : AspisR1CurrentCaller.transport.Variant) : AspisR1Stage2.transport.Variant :=
  match x with
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D
def phaseToStage (x : AspisR1CurrentCaller.verifier.Phase) : AspisR1Stage2.verifier.Phase :=
  match x with
  | .Parsed => .Parsed | .Semantic => .Semantic | .SemanticPart n => .SemanticPart n
  | .Prepare => .Prepare | .CheckpointRead => .CheckpointRead | .Merkle n => .Merkle n
  | .Query n => .Query n | .QueryPart n part => .QueryPart n part
  | .CheckpointWrite => .CheckpointWrite | .Relation => .Relation | .Final => .Final
def phaseToCaller (x : AspisR1Stage2.verifier.Phase) : AspisR1CurrentCaller.verifier.Phase :=
  match x with
  | .Parsed => .Parsed | .Semantic => .Semantic | .SemanticPart n => .SemanticPart n
  | .Prepare => .Prepare | .CheckpointRead => .CheckpointRead | .Merkle n => .Merkle n
  | .Query n => .Query n | .QueryPart n part => .QueryPart n part
  | .CheckpointWrite => .CheckpointWrite | .Relation => .Relation | .Final => .Final

def arrayWideToStage {n : Usize} (xs : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact n) :
    Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact n :=
  ⟨xs.val.map wideToStage, by simpa only [List.length_map] using xs.property⟩

def wideToFullViaClaim (x : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact) : FullWide := wideToStage x
theorem wideToFullViaClaim_eq_stage (x : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact) :
    wideToFullViaClaim x = wideToStage x := rfl

def scratchToStageViaClaim (xs : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    Array FullWide 29#usize := arrayWideToStage xs
theorem scratchToStageViaClaim_eq_stage (xs : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    scratchToStageViaClaim xs = arrayWideToStage xs := rfl

def m31ArrayToStage {n : Usize} (xs : Array AspisR1CurrentCaller.aspis_core.field.M31 n) :
    Array AspisR1Stage2.aspis_core.field.M31 n := ⟨xs.val, xs.property⟩
def cmArrayToStage {n : Usize} (xs : Array AspisR1CurrentCaller.aspis_core.field.CM31 n) :
    Array AspisR1Stage2.aspis_core.field.CM31 n := ⟨xs.val.map cmToStage, by simpa only [List.length_map] using xs.property⟩
def qmArrayToStage {n : Usize} (xs : Array AspisR1CurrentCaller.aspis_core.field.QM31 n) :
    Array AspisR1Stage2.aspis_core.field.QM31 n := ⟨xs.val.map qmToStage, by simpa only [List.length_map] using xs.property⟩
def circleArrayToStage {n : Usize} (xs : Array AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint n) :
    Array AspisR1Stage2.aspis_core.circle.SecureCirclePoint n := ⟨xs.val.map circleToStage, by simpa only [List.length_map] using xs.property⟩
def cmToCaller (x : AspisR1Stage2.aspis_core.field.CM31) : AspisR1CurrentCaller.aspis_core.field.CM31 := ⟨x.a,x.b⟩
def qmToCaller (x : AspisR1Stage2.aspis_core.field.QM31) : AspisR1CurrentCaller.aspis_core.field.QM31 :=
  ⟨cmToCaller x.c0,cmToCaller x.c1⟩
def wideToCaller (x : AspisR1Stage2.aspis_core.field.wide_exact.WideExact) : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact :=
  ⟨qmToCaller x.c0,qmToCaller x.c1⟩
def circleToCaller (x : AspisR1Stage2.aspis_core.circle.SecureCirclePoint) : AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint :=
  ⟨qmToCaller x.x,qmToCaller x.y⟩
def variantToCaller (x : AspisR1Stage2.transport.Variant) : AspisR1CurrentCaller.transport.Variant :=
  match x with | .S1 => .S1 | .S2 => .S2 | .D => .D

def arrayWideToCaller {n : Usize} (xs : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact n) :
    Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact n :=
  ⟨xs.val.map wideToCaller, by simpa only [List.length_map] using xs.property⟩
def qmArrayToCaller {n : Usize} (xs : Array AspisR1Stage2.aspis_core.field.QM31 n) :
    Array AspisR1CurrentCaller.aspis_core.field.QM31 n :=
  ⟨xs.val.map qmToCaller, by simpa only [List.length_map] using xs.property⟩
def circleArrayToCaller {n : Usize} (xs : Array AspisR1Stage2.aspis_core.circle.SecureCirclePoint n) :
    Array AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint n :=
  ⟨xs.val.map circleToCaller, by simpa only [List.length_map] using xs.property⟩
def preparedToCaller (p : AspisR1Stage2.verifier.Prepared) : AspisR1CurrentCaller.verifier.Prepared :=
  { variant := variantToCaller p.variant
    roots := p.roots
    gamma := wideToCaller p.gamma
    kappa := wideToCaller p.kappa
    alpha := arrayWideToCaller p.alpha
    rho := qmToCaller p.rho
    queries := p.queries
    semantic_alpha := qmArrayToCaller p.semantic_alpha
    z := circleArrayToCaller p.z
    claim := wideToCaller p.claim
    state := p.state }

def vecMapStageToCaller {α β : Type} (f : α → β) (xs : Aeneas.Std.alloc.vec.Vec α) :
    Aeneas.Std.alloc.vec.Vec β :=
  ⟨xs.val.map f, by simpa only [List.length_map] using xs.property⟩
def accumulatorStageToCaller (a : AspisR1Stage2.verifier.Accumulator) : AspisR1CurrentCaller.verifier.Accumulator :=
  { weights := vecMapStageToCaller qmToCaller a.weights, rhs := wideToCaller a.rhs,
    power := qmToCaller a.power, next := a.next }
def batchedWeightsStageToCaller (b : AspisR1Stage2.verifier.BatchedWeights) : AspisR1CurrentCaller.verifier.BatchedWeights :=
  { raw := vecMapStageToCaller id b.raw, terms := b.terms }

def preparedToStage (p : AspisR1CurrentCaller.verifier.Prepared) : AspisR1Stage2.verifier.Prepared :=
  { variant := variantToStage p.variant
    roots := p.roots
    gamma := wideToStage p.gamma
    kappa := wideToStage p.kappa
    alpha := arrayWideToStage p.alpha
    rho := qmToStage p.rho
    queries := p.queries
    semantic_alpha := qmArrayToStage p.semantic_alpha
    z := circleArrayToStage p.z
    claim := wideToStage p.claim
    state := p.state }

def vecMap {α β : Type} (f : α → β) (xs : Aeneas.Std.alloc.vec.Vec α) : Aeneas.Std.alloc.vec.Vec β :=
  ⟨xs.val.map f, by simpa only [List.length_map] using xs.property⟩
def accumulatorToStage (a : AspisR1CurrentCaller.verifier.Accumulator) : AspisR1Stage2.verifier.Accumulator :=
  { weights := vecMap qmToStage a.weights, rhs := wideToStage a.rhs,
    power := qmToStage a.power, next := a.next }
def batchedWeightsToStage (b : AspisR1CurrentCaller.verifier.BatchedWeights) : AspisR1Stage2.verifier.BatchedWeights :=
  { raw := vecMap id b.raw, terms := b.terms }
def geometryToStage (g : AspisR1CurrentCaller.verifier.QueryGeometry) : AspisR1Stage2.verifier.QueryGeometry :=
  { start := g.start, inverses := vecMap m31ArrayToStage g.inverses,
    line_z := vecMap (fun x : AspisR1CurrentCaller.aspis_core.field.M31 => x) g.line_z }


def errorToCaller (e : AspisR1Stage2.verifier.Error) : AspisR1CurrentCaller.verifier.Error :=
  match e with
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript | .Relation => .Relation
  | .Merkle => .Merkle | .Query => .Query | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def accumulatorToCaller (a : AspisR1Stage2.verifier.Accumulator) : AspisR1CurrentCaller.verifier.Accumulator :=
  { weights := vecMap (fun q : AspisR1Stage2.aspis_core.field.QM31 => ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩) a.weights
    rhs := ⟨⟨⟨a.rhs.c0.c0.a,a.rhs.c0.c0.b⟩,⟨a.rhs.c0.c1.a,a.rhs.c0.c1.b⟩⟩,
            ⟨⟨a.rhs.c1.c0.a,a.rhs.c1.c0.b⟩,⟨a.rhs.c1.c1.a,a.rhs.c1.c1.b⟩⟩⟩
    power := ⟨⟨a.power.c0.a,a.power.c0.b⟩,⟨a.power.c1.a,a.power.c1.b⟩⟩
    next := a.next }

def batchedWeightsToCaller (b : AspisR1Stage2.verifier.BatchedWeights) : AspisR1CurrentCaller.verifier.BatchedWeights :=
  { raw := vecMap id b.raw, terms := b.terms }

def queryLoopResultToCaller (r : Result (core.result.Result
    (AspisR1Stage2.verifier.Accumulator × AspisR1Stage2.verifier.BatchedWeights)
    AspisR1Stage2.verifier.Error)) : Result (core.result.Result
    (AspisR1CurrentCaller.verifier.Accumulator × AspisR1CurrentCaller.verifier.BatchedWeights)
    AspisR1CurrentCaller.verifier.Error) :=
  match r with
  | .ok (.Ok (a,b)) => .ok (.Ok (accumulatorToCaller a, batchedWeightsToCaller b))
  | .ok (.Err e) => .ok (.Err (errorToCaller e))
  | .fail e => .fail e
  | .div => .div

def stage2QueryLoopAdapter (call : AspisR1Stage2.QueryCall) :
    Slice U8 → AspisR1CurrentCaller.verifier.Prepared →
    AspisR1CurrentCaller.verifier.Accumulator → Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize →
    Option (AspisR1CurrentCaller.verifier.Phase → Result Unit) → AspisR1CurrentCaller.verifier.QueryGeometry →
    AspisR1CurrentCaller.verifier.BatchedWeights → Usize → Result (core.result.Result
      (AspisR1CurrentCaller.verifier.Accumulator × AspisR1CurrentCaller.verifier.BatchedWeights)
      AspisR1CurrentCaller.verifier.Error) := by
  intro proof p a g obs geom pending end1
  exact queryLoopResultToCaller (AspisR1Stage2.verifier.candidate.query_loop call proof
    (preparedToStage p) (accumulatorToStage a) (arrayWideToStage g) (obs.map (fun f => fun phase => f (phaseToCaller phase)))
    (geometryToStage geom) (batchedWeightsToStage pending) end1)

theorem queryLoopResultToCaller_ok_inv
    {r : Result (core.result.Result
      (AspisR1Stage2.verifier.Accumulator × AspisR1Stage2.verifier.BatchedWeights)
      AspisR1Stage2.verifier.Error)}
    {a : AspisR1CurrentCaller.verifier.Accumulator}
    {b : AspisR1CurrentCaller.verifier.BatchedWeights}
    (h : queryLoopResultToCaller r = .ok (.Ok (a,b))) :
    ∃ aS bS, r = .ok (.Ok (aS,bS)) ∧ accumulatorToCaller aS = a ∧ batchedWeightsToCaller bS = b := by
  cases r with
  | ok res =>
    cases res with
    | Ok pair =>
      rcases pair with ⟨aS,bS⟩
      simp only [queryLoopResultToCaller] at h
      injection h with hcore
      injection hcore with hp
      rcases Prod.mk.inj hp with ⟨ha,hb⟩
      exact ⟨aS,bS,rfl,ha,hb⟩
    | Err e => simp [queryLoopResultToCaller, errorToCaller] at h
  | fail e => simp [queryLoopResultToCaller] at h
  | div => simp [queryLoopResultToCaller] at h

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem afterPrepared_success_query_loop_and_new {H : Type}
    (ops : AspisR1CallerV4Tx1OpsCut.Ops H)
    (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (prepared : AspisR1CurrentCaller.verifier.Prepared)
    (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (proof public_bytes : Slice U8) (k : Usize) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (bytes : Aeneas.Std.alloc.vec.Vec U8)
    (h : AspisR1CallerV4Tx1OpsCut.afterPrepared ops inst prepared scratch proof public_bytes k hash obs = .ok (.Ok bytes)) :
    ∃ initialAcc geom pending outputAcc outputPending,
      ops.accumulatorNew AspisR1CurrentCaller.transport.Variant.S2 = .ok (.Ok initialAcc) ∧
      ops.queryLoop proof prepared initialAcc scratch obs geom pending k =
        .ok (.Ok (outputAcc, outputPending)) := by
  unfold AspisR1CallerV4Tx1OpsCut.afterPrepared at h
  obtain ⟨r3, hr3, h⟩ := bind_ok_inv h
  cases r3 with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  | Ok val1 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    obtain ⟨_, hmark, h⟩ := bind_ok_inv h
    obtain ⟨i, hi, h⟩ := bind_ok_inv h
    obtain ⟨i1, hi1, h⟩ := bind_ok_inv h
    obtain ⟨s, hs, h⟩ := bind_ok_inv h
    obtain ⟨r4, hr4, h⟩ := bind_ok_inv h
    obtain ⟨foldedRoot, hfolded, h⟩ := bind_ok_inv h
    obtain ⟨r5, hr5, h⟩ := bind_ok_inv h
    cases r5 with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok _ =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      obtain ⟨_, hmark2, h⟩ := bind_ok_inv h
      obtain ⟨r6, hr6, h⟩ := bind_ok_inv h
      cases r6 with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
      | Ok geom =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
        obtain ⟨r7, hr7, h⟩ := bind_ok_inv h
        cases r7 with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
        | Ok pending =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
          obtain ⟨r8, hr8, h⟩ := bind_ok_inv h
          cases r8 with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
          | Ok pair =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
            rcases pair with ⟨acc, pending'⟩
            exact ⟨val1, geom, pending, acc, pending', by simpa using hr3, hr8⟩

theorem tx1_success_same_stage2_query {H : Type}
    (ops : AspisR1CallerV4Tx1OpsCut.Ops H)
    (call : AspisR1Stage2.QueryCall)
    (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (bytes : Aeneas.Std.alloc.vec.Vec U8)
    (h : AspisR1CallerV4Tx1OpsCut.tx1
      { ops with queryLoop := stage2QueryLoopAdapter call }
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    ∃ parsed zero prepared scratch initialAcc geom pending outputAcc outputPending outputAccS outputPendingS,
      ops.parseShape proof = .ok (.Ok parsed) ∧
      ops.canonicalScan proof = .ok (.Ok ()) ∧
      ops.zero = .ok zero ∧
      ops.prepare inst public1 proof hash obs (Array.repeat 29#usize zero) =
        .ok (.Ok prepared, scratch) ∧
      AspisR1Stage2.verifier.candidate.query_loop call proof
        (preparedToStage prepared) (accumulatorToStage initialAcc) (arrayWideToStage scratch)
        (obs.map (fun f => fun phase => f (phaseToCaller phase)))
        (geometryToStage geom) (batchedWeightsToStage pending) k =
          .ok (.Ok (outputAccS,outputPendingS)) ∧
      ops.accumulatorNew AspisR1CurrentCaller.transport.Variant.S2 = .ok (.Ok initialAcc) ∧
      accumulatorToCaller outputAccS = outputAcc ∧
      batchedWeightsToCaller outputPendingS = outputPending := by
  obtain ⟨parsed,zero,prepared,scratch,hparse,hscan,hzero,hprepare,hafter⟩ :=
    AspisR1CallerV4Tx1OpsCut.tx1_success_prepare_same_suffix
      { ops with queryLoop := stage2QueryLoopAdapter call }
      inst public1 public_bytes proof k hash obs bytes h
  obtain ⟨initialAcc,geom,pending,outputAcc,outputPending,hnew,hquery⟩ :=
    afterPrepared_success_query_loop_and_new
      { ops with queryLoop := stage2QueryLoopAdapter call }
      inst prepared scratch proof public_bytes k hash obs bytes hafter
  obtain ⟨outputAccS,outputPendingS,hloop,hacc,hpending⟩ := queryLoopResultToCaller_ok_inv hquery
  exact ⟨parsed,zero,prepared,scratch,initialAcc,geom,pending,outputAcc,outputPending,outputAccS,outputPendingS,
    hparse,hscan,hzero,hprepare, by simpa [stage2QueryLoopAdapter] using hloop,
    hnew,hacc,hpending⟩

theorem wide_roundtrip (x : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact) :
    wideToCaller (wideToStage x) = x := by cases x <;> rfl

theorem qm_roundtrip (x : AspisR1CurrentCaller.aspis_core.field.QM31) :
    qmToCaller (qmToStage x) = x := by cases x <;> rfl

theorem circle_roundtrip (x : AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint) :
    circleToCaller (circleToStage x) = x := by cases x <;> rfl

theorem arrayWide_roundtrip {n : Usize}
    (xs : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact n) :
    arrayWideToCaller (arrayWideToStage xs) = xs := by
  apply Subtype.ext
  simp only [arrayWideToCaller, arrayWideToStage]
  rw [List.map_map]
  simpa only [List.map_id] using (List.map_congr_left
    (l := xs.val) (f := wideToCaller ∘ wideToStage) (g := id)
    (by intro x hx; exact wide_roundtrip x))

theorem qmArray_roundtrip {n : Usize}
    (xs : Array AspisR1CurrentCaller.aspis_core.field.QM31 n) :
    qmArrayToCaller (qmArrayToStage xs) = xs := by
  apply Subtype.ext
  simp only [qmArrayToCaller, qmArrayToStage]
  rw [List.map_map]
  simpa only [List.map_id] using (List.map_congr_left
    (l := xs.val) (f := qmToCaller ∘ qmToStage) (g := id)
    (by intro x hx; exact qm_roundtrip x))

theorem circleArray_roundtrip {n : Usize}
    (xs : Array AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint n) :
    circleArrayToCaller (circleArrayToStage xs) = xs := by
  apply Subtype.ext
  simp only [circleArrayToCaller, circleArrayToStage]
  rw [List.map_map]
  simpa only [List.map_id] using (List.map_congr_left
    (l := xs.val) (f := circleToCaller ∘ circleToStage) (g := id)
    (by intro x hx; exact circle_roundtrip x))

theorem prepared_roundtrip (p : AspisR1CurrentCaller.verifier.Prepared) :
    preparedToCaller (preparedToStage p) = p := by
  cases p with
  | mk variant roots gamma kappa alpha rho queries semantic_alpha z claim state =>
    cases variant <;>
      simp [preparedToCaller,preparedToStage,variantToCaller,variantToStage,
        wide_roundtrip,qm_roundtrip,circle_roundtrip,arrayWide_roundtrip,
        qmArray_roundtrip,circleArray_roundtrip]

theorem prepared_gamma_maps_exact (p : AspisR1CurrentCaller.verifier.Prepared) :
    (preparedToStage p).gamma = wideToStage p.gamma := rfl
theorem prepared_all_fields_roundtrip (p : AspisR1CurrentCaller.verifier.Prepared) :
    (preparedToStage p).variant = variantToStage p.variant ∧
    (preparedToStage p).roots = p.roots ∧
    (preparedToStage p).gamma = wideToStage p.gamma ∧
    (preparedToStage p).kappa = wideToStage p.kappa ∧
    (preparedToStage p).alpha = arrayWideToStage p.alpha ∧
    (preparedToStage p).rho = qmToStage p.rho ∧
    (preparedToStage p).queries = p.queries ∧
    (preparedToStage p).semantic_alpha = qmArrayToStage p.semantic_alpha ∧
    (preparedToStage p).z = circleArrayToStage p.z ∧
    (preparedToStage p).claim = wideToStage p.claim ∧
    (preparedToStage p).state = p.state := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms prepared_all_fields_roundtrip
#print axioms tx1_success_same_stage2_query
end AspisR1S4CallerStage2CarrierV1
