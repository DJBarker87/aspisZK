import R1Z.ProverCommitPolicies25
import Query31ConcreteWordsDriverChain
/-! Concrete query policy and exact extracted caller factorization. The
policy uses the retained concrete LE/mask decoder and first-stop model scan;
source iterator identification remains a distinct P6/source obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitQuery26
open Aeneas Aeneas.Std Result AspisR1SimControl21
open Query31ExplicitListLoop Query31ExplicitScanBody Query31ModelScanCall
open Query31ModelDriverChain Query31ConcreteWordsDriverChain
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks := Array Bytes32 8#usize
abbrev Queries := Array U32 22#usize
abbrev Scan := AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan

def initial : Scan := ⟨Array.repeat 22#usize 0#u32,0#usize,0#usize⟩

theorem initial_valid : validState initial := by
  apply validState_of_bounds <;> decide

def raw (blocks advances : Blocks) :=
  AspisR1Query31Transcript.queries_from_pairs_with_scan
    (modelScanFn actualQueryWords) initial blocks advances

def query (blocks advances : Blocks) : Result (core.result.Result
    (Queries × Bytes32) verifier.Error) := do
  let r ← raw blocks advances
  match r with
  | .Ok value => ok (core.result.Result.Ok value)
  | .Err _ => ok (core.result.Result.Err verifier.Error.Transcript)

def policy : transcript.control21.Policy Unit := ProverCommitPolicies25.policy query

theorem installed (blocks advances : Blocks) :
    policy.queries blocks advances = query blocks advances := rfl

/-- The installed query callback exposes the actual selected first-stop
source-shaped trace, not an arbitrary supplied query function. -/
theorem success (blocks advances : Blocks) (q : Queries) (next : Bytes32)
    (h : policy.queries blocks advances = ok (.Ok (q,next))) :
    AspisR1Query31Transcript.DriverTrace (modelScanFn actualQueryWords)
      blocks advances initial q next ∧
    ∃ evidence sf, Q22ScanChain actualQueryWords blocks initial evidence sf ∧
      evidence.length ≤ 8 ∧ validState sf ∧
      ∀ e ∈ evidence, e.words.val = (List.range 8).map
        (fun j => AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
          (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord e.bytes j)) := by
  have hr : raw blocks advances = ok (.Ok (q,next)) := by
    change (do let r ← raw blocks advances
               match r with
               | .Ok value => ok (core.result.Result.Ok value)
               | .Err _ => ok (core.result.Result.Err verifier.Error.Transcript)) = _ at h
    cases he : raw blocks advances with
    | fail e => simp only [he,bind_tc_fail] at h; cases h
    | div => simp only [he,bind_tc_div] at h; cases h
    | ok r =>
      cases r with
      | Err e => simp only [he,bind_tc_ok] at h; cases h
      | Ok value =>
        simp only [he,bind_tc_ok,Result.ok.injEq,core.result.Result.Ok.injEq] at h
        exact congrArg (fun v => ok (core.result.Result.Ok v)) h
  exact ⟨AspisR1Query31Transcript.successful_driver_has_trace _ _ _ _ _ _ hr,
    successful_driver_has_concrete_q22_chain blocks advances initial q next initial_valid hr⟩

/-- The source error mapping is explicit and retains every machine error
before the sampler result; a scan rejection maps to Transcript. -/
theorem rejection (blocks advances : Blocks)
    (error : AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError)
    (h : raw blocks advances = ok (.Err error)) :
    policy.queries blocks advances = ok (core.result.Result.Err verifier.Error.Transcript) := by
  simp only [policy,ProverCommitPolicies25.policy,query,h,bind_tc_ok]

def materialize {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
    (PolicyInst : transcript.control21.Policy Unit)
    (self : transcript.control21.Transcript H Unit) (row : U8) (payload : Slice U8) :
    Result (transcript.control21.Transcript H Unit × Blocks × Blocks) := do
  let self1 ←
    transcript.control21.Transcript.absorb aspis_coredigestDigest32Inst
      PolicyInst self row payload
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let s ← lift (Array.to_slice self1.state)
  let s1 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s2 ← lift (Array.to_slice (Array.make 2#usize [ s, s1 ]))
  let a1 ← aspis_coredigestDigest32Inst.digest self1.hash s2
  let (_, index_mut_back) ← Array.index_mut_usize blocks 0#usize
  let s3 ← lift (Array.to_slice self1.state)
  let s4 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s5 ← lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
  let a2 ← aspis_coredigestDigest32Inst.digest self1.hash s5
  let blocks1 := index_mut_back a2
  let state ← Array.index_usize blocks1 0#usize
  let s6 ← lift (Array.to_slice state)
  let s7 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s8 ← lift (Array.to_slice (Array.make 2#usize [ s6, s7 ]))
  let a3 ← aspis_coredigestDigest32Inst.digest self1.hash s8
  let blocks2 := index_mut_back a1
  let blocks3 ← Array.update blocks2 1#usize a3
  let s9 ← lift (Array.to_slice state)
  let s10 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s11 ← lift (Array.to_slice (Array.make 2#usize [ s9, s10 ]))
  let a4 ← aspis_coredigestDigest32Inst.digest self1.hash s11
  let blocks4 ← Array.update blocks1 1#usize a4
  let state1 ← Array.index_usize blocks4 1#usize
  let s12 ← lift (Array.to_slice state1)
  let s13 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s14 ← lift (Array.to_slice (Array.make 2#usize [ s12, s13 ]))
  let a5 ← aspis_coredigestDigest32Inst.digest self1.hash s14
  let blocks5 ← Array.update blocks3 2#usize a5
  let s15 ← lift (Array.to_slice state1)
  let s16 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s17 ← lift (Array.to_slice (Array.make 2#usize [ s15, s16 ]))
  let a6 ← aspis_coredigestDigest32Inst.digest self1.hash s17
  let blocks6 ← Array.update blocks4 2#usize a6
  let state2 ← Array.index_usize blocks6 2#usize
  let s18 ← lift (Array.to_slice state2)
  let s19 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s20 ← lift (Array.to_slice (Array.make 2#usize [ s18, s19 ]))
  let a7 ← aspis_coredigestDigest32Inst.digest self1.hash s20
  let blocks7 ← Array.update blocks5 3#usize a7
  let s21 ← lift (Array.to_slice state2)
  let s22 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s23 ← lift (Array.to_slice (Array.make 2#usize [ s21, s22 ]))
  let a8 ← aspis_coredigestDigest32Inst.digest self1.hash s23
  let blocks8 ← Array.update blocks6 3#usize a8
  let state3 ← Array.index_usize blocks8 3#usize
  let s24 ← lift (Array.to_slice state3)
  let s25 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s26 ← lift (Array.to_slice (Array.make 2#usize [ s24, s25 ]))
  let a9 ← aspis_coredigestDigest32Inst.digest self1.hash s26
  let blocks9 ← Array.update blocks7 4#usize a9
  let s27 ← lift (Array.to_slice state3)
  let s28 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s29 ← lift (Array.to_slice (Array.make 2#usize [ s27, s28 ]))
  let a10 ← aspis_coredigestDigest32Inst.digest self1.hash s29
  let blocks10 ← Array.update blocks8 4#usize a10
  let state4 ← Array.index_usize blocks10 4#usize
  let s30 ← lift (Array.to_slice state4)
  let s31 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s32 ← lift (Array.to_slice (Array.make 2#usize [ s30, s31 ]))
  let a11 ← aspis_coredigestDigest32Inst.digest self1.hash s32
  let blocks11 ← Array.update blocks9 5#usize a11
  let s33 ← lift (Array.to_slice state4)
  let s34 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s35 ← lift (Array.to_slice (Array.make 2#usize [ s33, s34 ]))
  let a12 ← aspis_coredigestDigest32Inst.digest self1.hash s35
  let blocks12 ← Array.update blocks10 5#usize a12
  let state5 ← Array.index_usize blocks12 5#usize
  let s36 ← lift (Array.to_slice state5)
  let s37 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s38 ← lift (Array.to_slice (Array.make 2#usize [ s36, s37 ]))
  let a13 ← aspis_coredigestDigest32Inst.digest self1.hash s38
  let blocks13 ← Array.update blocks11 6#usize a13
  let s39 ← lift (Array.to_slice state5)
  let s40 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s41 ← lift (Array.to_slice (Array.make 2#usize [ s39, s40 ]))
  let a14 ← aspis_coredigestDigest32Inst.digest self1.hash s41
  let blocks14 ← Array.update blocks12 6#usize a14
  let state6 ← Array.index_usize blocks14 6#usize
  let s42 ← lift (Array.to_slice state6)
  let s43 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s44 ← lift (Array.to_slice (Array.make 2#usize [ s42, s43 ]))
  let a15 ← aspis_coredigestDigest32Inst.digest self1.hash s44
  let blocks15 ← Array.update blocks13 7#usize a15
  let s45 ← lift (Array.to_slice state6)
  let s46 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s47 ← lift (Array.to_slice (Array.make 2#usize [ s45, s46 ]))
  let a16 ← aspis_coredigestDigest32Inst.digest self1.hash s47
  let blocks16 ← Array.update blocks14 7#usize a16
  let _ ← Array.index_usize blocks16 7#usize
  ok (self1,blocks15,blocks16)

def finish {H : Type} (self1 : transcript.control21.Transcript H Unit)
    (blocks15 blocks16 : Blocks) :
    Result (core.result.Result Queries verifier.Error × transcript.control21.Transcript H Unit) := do
  let r ← query blocks15 blocks16
  match r with
  | core.result.Result.Ok v =>
    let (q, state7) := v
    let u ← Array.index_usize q 0#usize
    let we ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u
    let v1 ← alloc.vec.Vec.push self1.trace (5#u16, 0#usize, we)
    let u1 ← Array.index_usize q 1#usize
    let we1 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u1
    let v2 ← alloc.vec.Vec.push v1 (5#u16, 1#usize, we1)
    let u2 ← Array.index_usize q 2#usize
    let we2 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u2
    let v3 ← alloc.vec.Vec.push v2 (5#u16, 2#usize, we2)
    let u3 ← Array.index_usize q 3#usize
    let we3 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u3
    let v4 ← alloc.vec.Vec.push v3 (5#u16, 3#usize, we3)
    let u4 ← Array.index_usize q 4#usize
    let we4 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u4
    let v5 ← alloc.vec.Vec.push v4 (5#u16, 4#usize, we4)
    let u5 ← Array.index_usize q 5#usize
    let we5 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u5
    let v6 ← alloc.vec.Vec.push v5 (5#u16, 5#usize, we5)
    let u6 ← Array.index_usize q 6#usize
    let we6 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u6
    let v7 ← alloc.vec.Vec.push v6 (5#u16, 6#usize, we6)
    let u7 ← Array.index_usize q 7#usize
    let we7 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u7
    let v8 ← alloc.vec.Vec.push v7 (5#u16, 7#usize, we7)
    let u8 ← Array.index_usize q 8#usize
    let we8 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u8
    let v9 ← alloc.vec.Vec.push v8 (5#u16, 8#usize, we8)
    let u9 ← Array.index_usize q 9#usize
    let we9 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u9
    let v10 ← alloc.vec.Vec.push v9 (5#u16, 9#usize, we9)
    let u10 ← Array.index_usize q 10#usize
    let we10 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u10
    let v11 ← alloc.vec.Vec.push v10 (5#u16, 10#usize, we10)
    let u11 ← Array.index_usize q 11#usize
    let we11 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u11
    let v12 ← alloc.vec.Vec.push v11 (5#u16, 11#usize, we11)
    let u12 ← Array.index_usize q 12#usize
    let we12 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u12
    let v13 ← alloc.vec.Vec.push v12 (5#u16, 12#usize, we12)
    let u13 ← Array.index_usize q 13#usize
    let we13 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u13
    let v14 ← alloc.vec.Vec.push v13 (5#u16, 13#usize, we13)
    let u14 ← Array.index_usize q 14#usize
    let we14 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u14
    let v15 ← alloc.vec.Vec.push v14 (5#u16, 14#usize, we14)
    let u15 ← Array.index_usize q 15#usize
    let we15 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u15
    let v16 ← alloc.vec.Vec.push v15 (5#u16, 15#usize, we15)
    let u16 ← Array.index_usize q 16#usize
    let we16 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u16
    let v17 ← alloc.vec.Vec.push v16 (5#u16, 16#usize, we16)
    let u17 ← Array.index_usize q 17#usize
    let we17 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u17
    let v18 ← alloc.vec.Vec.push v17 (5#u16, 17#usize, we17)
    let u18 ← Array.index_usize q 18#usize
    let we18 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u18
    let v19 ← alloc.vec.Vec.push v18 (5#u16, 18#usize, we18)
    let u19 ← Array.index_usize q 19#usize
    let we19 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u19
    let v20 ← alloc.vec.Vec.push v19 (5#u16, 19#usize, we19)
    let u20 ← Array.index_usize q 20#usize
    let we20 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u20
    let v21 ← alloc.vec.Vec.push v20 (5#u16, 20#usize, we20)
    let u21 ← Array.index_usize q 21#usize
    let we21 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        u21
    let v22 ← alloc.vec.Vec.push v21 (5#u16, 21#usize, we21)
    ok (core.result.Result.Ok q, { self1 with state := state7, trace := v22 })
  | core.result.Result.Err e => ok (core.result.Result.Err e, self1)


/-- Literal extracted hash schedule, including all eight materialized pairs,
followed by the concrete first-stop callback and exact trace continuation. -/
theorem caller {H : Type} (hash : aspis_core.digest.Digest32 H)
    (state : transcript.control21.Transcript H Unit) (row : U8) (payload : Slice U8) :
    transcript.control21.Transcript.queries hash policy state row payload =
      (do let (absorbed,blocks,advances) ← materialize hash policy state row payload
          finish absorbed blocks advances) := by
  unfold transcript.control21.Transcript.queries materialize
  repeat
    rw [Aeneas.Std.bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro v hv
    try (change (_ × _) at v; rcases v with ⟨v1,v2⟩)
    try dsimp only [Aeneas.Std.uncurry]
  rw [bind_tc_ok]
  rfl

/-- On query rejection the caller retains the absorbed state and previous
trace; no query trace entries or rho call are manufactured. -/
theorem finish_rejection {H : Type} (state : transcript.control21.Transcript H Unit)
    (blocks advances : Blocks)
    (h : query blocks advances = ok (core.result.Result.Err verifier.Error.Transcript)) :
    finish state blocks advances = ok (.Err verifier.Error.Transcript,state) := by
  simp only [finish,h,bind_tc_ok]

#print axioms initial_valid
#print axioms installed
#print axioms success
#print axioms rejection
#print axioms caller
#print axioms finish_rejection
end R1Z.ProverCommitQuery26
