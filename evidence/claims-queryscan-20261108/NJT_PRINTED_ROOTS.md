# Printed root statements

Exact definitions, quantifiers and hidden cut/domain fields from L047; these are statement inspections, not native closure claims.129 is support only.

```text
def AspisR1.NJT_ClaimsRoot.Packet : Aeneas.Std.Slice Aeneas.Std.U8 → Prop :=
fun bytes =>
  match AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
  | Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok pre) =>
    AspisR1.ClaimsUnrolledFinish.toMainStatus
          (AspisR1.NJT_ClaimsRef_Value.unbox
            (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
              (AspisR1.ClaimsUnrolledFinish.fromMainPrefix (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))) =
        AspisR1.ClaimsUnrolledFinish.claims AspisR1.NJT_ClaimsRef_Value.std
          (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) ∧
      ∃ record,
        (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
            Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok record) ∧
          record.row = 25#u8 ∧
            (↑record.framed).length = 3717 ∧
              ∀ (p off : Aeneas.Std.Usize),
                ↑p < 3 →
                  ↑off = ↑p * 29 →
                    ∃ out,
                      AspisS1ExtractedRoundChildren.decodeMain 29#usize record off =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok out)
  | x => True
theorem AspisR1.NJT_ClaimsRoot.claims : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8),
  AspisR1.NJT_ClaimsRoot.Packet bytes :=
fun bytes =>
  id
    (Aeneas.Std.Result.casesOn (motive := fun t =>
      AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = t →
        match AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
        | Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok pre) =>
          AspisR1.ClaimsUnrolledFinish.toMainStatus
                (AspisR1.NJT_ClaimsRef_Value.unbox
                  (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
                    (AspisR1.ClaimsUnrolledFinish.fromMainPrefix
                      (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))) =
              AspisR1.ClaimsUnrolledFinish.claims AspisR1.NJT_ClaimsRef_Value.std
                (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) ∧
            ∃ record,
              (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok record) ∧
                record.row = 25#u8 ∧
                  (↑record.framed).length = 3717 ∧
                    ∀ (p off : Aeneas.Std.Usize),
                      ↑p < 3 →
                        ↑off = ↑p * 29 →
                          ∃ out,
                            AspisS1ExtractedRoundChildren.decodeMain 29#usize record off =
                              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok out)
        | x => True)
      (AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes)
      (fun result h =>
        Eq.ndrec (motive := fun result =>
          AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = result →
            match result with
            | Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok pre) =>
              AspisR1.ClaimsUnrolledFinish.toMainStatus
                    (AspisR1.NJT_ClaimsRef_Value.unbox
                      (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
                        (AspisR1.ClaimsUnrolledFinish.fromMainPrefix
                          (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))) =
                  AspisR1.ClaimsUnrolledFinish.claims AspisR1.NJT_ClaimsRef_Value.std
                    (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) ∧
                ∃ record,
                  (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
                      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok record) ∧
                    record.row = 25#u8 ∧
                      (↑record.framed).length = 3717 ∧
                        ∀ (p off : Aeneas.Std.Usize),
                          ↑p < 3 →
                            ↑off = ↑p * 29 →
                              ∃ out,
                                AspisS1ExtractedRoundChildren.decodeMain 29#usize record off =
                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok out)
            | x => True)
          (fun parsed =>
            Aeneas.Std.core.result.Result.casesOn (motive := fun t =>
              result = t →
                match Aeneas.Std.Result.ok result with
                | Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok pre) =>
                  AspisR1.ClaimsUnrolledFinish.toMainStatus
                        (AspisR1.NJT_ClaimsRef_Value.unbox
                          (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
                            (AspisR1.ClaimsUnrolledFinish.fromMainPrefix
                              (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))) =
                      AspisR1.ClaimsUnrolledFinish.claims AspisR1.NJT_ClaimsRef_Value.std
                        (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) ∧
                    ∃ record,
                      (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
                          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok record) ∧
                        record.row = 25#u8 ∧
                          (↑record.framed).length = 3717 ∧
                            ∀ (p off : Aeneas.Std.Usize),
                              ↑p < 3 →
                                ↑off = ↑p * 29 →
                                  ∃ out,
                                    AspisS1ExtractedRoundChildren.decodeMain 29#usize record off =
                                      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok out)
                | x => True)
              result
              (fun pre h =>
                Eq.ndrec (motive := fun result =>
                  AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = Aeneas.Std.Result.ok result →
                    match Aeneas.Std.Result.ok result with
                    | Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok pre) =>
                      AspisR1.ClaimsUnrolledFinish.toMainStatus
                            (AspisR1.NJT_ClaimsRef_Value.unbox
                              (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
                                (AspisR1.ClaimsUnrolledFinish.fromMainPrefix
                                  (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))) =
                          AspisR1.ClaimsUnrolledFinish.claims AspisR1.NJT_ClaimsRef_Value.std
                            (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) ∧
                        ∃ record,
                          (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
                              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok record) ∧
                            record.row = 25#u8 ∧
                              (↑record.framed).length = 3717 ∧
                                ∀ (p off : Aeneas.Std.Usize),
                                  ↑p < 3 →
                                    ↑off = ↑p * 29 →
                                      ∃ out,
                                        AspisS1ExtractedRoundChildren.decodeMain 29#usize record off =
                                          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok out)
                    | x => True)
                  (fun parsed =>
                    ⟨AspisR1.NJT_ClaimsRoot.reference (AspisR1PublicPreparation.PrefixAdapter.fromOld pre),
                      let ⟨record, h✝⟩ := AspisR1.NJT_QClaimsCanonical.claims bytes pre parsed
                      let ⟨getter, right✝⟩ := h✝
                      let ⟨row, decoded⟩ := right✝
                      let ⟨same, h✝¹⟩ := AspisR1.NJG_ClaimsGeometry.producer bytes pre parsed
                      let ⟨call, right✝¹⟩ := h✝¹
                      let ⟨tag, framed⟩ := right✝¹
                      have equal :=
                        Aeneas.Std.core.result.Result.Ok.inj
                          (Aeneas.Std.Result.ok.inj (Eq.trans (Eq.symm call) getter));
                      Eq.ndrec (motive := fun same =>
                        (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
                            Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok same) →
                          same.row = 25#u8 →
                            (↑same.framed).length = 3717 →
                              ∃ record,
                                (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
                                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok record) ∧
                                  record.row = 25#u8 ∧
                                    (↑record.framed).length = 3717 ∧
                                      ∀ (p off : Aeneas.Std.Usize),
                                        ↑p < 3 →
                                          ↑off = ↑p * 29 →
                                            ∃ out,
                                              AspisS1ExtractedRoundChildren.decodeMain 29#usize record off =
                                                Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok out))
                        (fun call tag framed => Exists.intro record ⟨getter, ⟨row, ⟨framed, decoded⟩⟩⟩) (Eq.symm equal)
                        call tag framed⟩)
                  (Eq.symm h) parsed)
              (fun e h =>
                Eq.ndrec (motive := fun result =>
                  AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = Aeneas.Std.Result.ok result →
                    match Aeneas.Std.Result.ok result with
                    | Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok pre) =>
                      AspisR1.ClaimsUnrolledFinish.toMainStatus
                            (AspisR1.NJT_ClaimsRef_Value.unbox
                              (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
                                (AspisR1.ClaimsUnrolledFinish.fromMainPrefix
                                  (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))) =
                          AspisR1.ClaimsUnrolledFinish.claims AspisR1.NJT_ClaimsRef_Value.std
                            (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) ∧
                        ∃ record,
                          (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
                              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok record) ∧
                            record.row = 25#u8 ∧
                              (↑record.framed).length = 3717 ∧
                                ∀ (p off : Aeneas.Std.Usize),
                                  ↑p < 3 →
                                    ↑off = ↑p * 29 →
                                      ∃ out,
                                        AspisS1ExtractedRoundChildren.decodeMain 29#usize record off =
                                          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok out)
                    | x => True)
                  (fun parsed => True.intro) (Eq.symm h) parsed)
              (Eq.refl result))
          (Eq.symm h) (Eq.refl (AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes)))
      (fun e h =>
        Eq.ndrec (motive := fun result =>
          AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = result →
            match result with
            | Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok pre) =>
              AspisR1.ClaimsUnrolledFinish.toMainStatus
                    (AspisR1.NJT_ClaimsRef_Value.unbox
                      (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
                        (AspisR1.ClaimsUnrolledFinish.fromMainPrefix
                          (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))) =
                  AspisR1.ClaimsUnrolledFinish.claims AspisR1.NJT_ClaimsRef_Value.std
                    (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) ∧
                ∃ record,
                  (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
                      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok record) ∧
                    record.row = 25#u8 ∧
                      (↑record.framed).length = 3717 ∧
                        ∀ (p off : Aeneas.Std.Usize),
                          ↑p < 3 →
                            ↑off = ↑p * 29 →
                              ∃ out,
                                AspisS1ExtractedRoundChildren.decodeMain 29#usize record off =
                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok out)
            | x => True)
          (fun parsed => True.intro) (Eq.symm h) (Eq.refl (AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes)))
      (fun h =>
        Eq.ndrec (motive := fun result =>
          AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = result →
            match result with
            | Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok pre) =>
              AspisR1.ClaimsUnrolledFinish.toMainStatus
                    (AspisR1.NJT_ClaimsRef_Value.unbox
                      (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
                        (AspisR1.ClaimsUnrolledFinish.fromMainPrefix
                          (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))) =
                  AspisR1.ClaimsUnrolledFinish.claims AspisR1.NJT_ClaimsRef_Value.std
                    (AspisR1PublicPreparation.PrefixAdapter.fromOld pre) ∧
                ∃ record,
                  (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
                      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok record) ∧
                    record.row = 25#u8 ∧
                      (↑record.framed).length = 3717 ∧
                        ∀ (p off : Aeneas.Std.Usize),
                          ↑p < 3 →
                            ↑off = ↑p * 29 →
                              ∃ out,
                                AspisS1ExtractedRoundChildren.decodeMain 29#usize record off =
                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok out)
            | x => True)
          (fun parsed => True.intro) (Eq.symm h) (Eq.refl (AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes)))
      (Eq.refl (AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes)))
def AspisR1.NJT_ClaimsRef_Value.std : AspisR1.ClaimsUnrolledFinish.StdCalls :=
{ reserve := fun {T} x v x_1 => Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (), v),
  intoBox := fun {T} x v => Aeneas.Std.Result.ok v }
theorem AspisR1.NJT_AllocationLift.named_allocator : ∀ {A : Type} (allocator : AspisR1.S2W_D189Wrappers.Allocator A)
  (initial : A) (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix),
  AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok pre) →
    AspisR1.NJT_AllocationLift.before (allocator.allocate initial 1392)
        (AspisR1.NJT_ClaimsRef_Value.unbox
          (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
            (AspisR1.ClaimsUnrolledFinish.fromMainPrefix (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))) =
      AspisR1.NJT_AllocationLift.after (allocator.allocate initial 1392)
        (AspisR1.NJT_ClaimsRef_Value.unbox
          (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
            (AspisR1.ClaimsUnrolledFinish.fromMainPrefix (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))) :=
fun {A} allocator initial bytes pre parsed =>
  let ⟨value, pure⟩ := AspisR1.NJT_AllocationLift.pure_success bytes pre parsed
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          AspisR1.NJT_AllocationLift.before (allocator.allocate initial 1392) _a =
            AspisR1.NJT_AllocationLift.after (allocator.allocate initial 1392) _a)
        pure))
    (AspisR1.NJT_AllocationLift.commute (allocator.allocate initial 1392) (Aeneas.Std.core.result.Result.Ok value))
def AspisR1.NJT_QLeaves.RankCut : AspisR1.NJT_QBase.Bytes → AspisR1.NJT_QBase.Words → Prop :=
fun b out => ∀ (k : Fin 8), (↑out)[↑k] = (↑(AspisR1.NJT_QBase.rank b))[↑k]
def AspisR1.NJT_QLeaves.WordsCut : AspisR1.NJT_QBase.Bytes → AspisR1.NJT_QBase.Words → Prop :=
fun b out => ∀ (k : Fin 8), (↑out)[↑k] = (↑(AspisR1.NJT_QBase.words b))[↑k]
def AspisR1.NJT_QLeaves.FinishCut : AspisR1.NJT_QBase.State → AspisR1.NJT_QBase.Finish → Prop :=
fun s out =>
  ↑s.accepted_len ≤ 22 ∧
    ↑s.draws ≤ 64 ∧
      match out with
      | Aeneas.Std.core.result.Result.Ok q => s.accepted_len = 22#usize ∧ ∀ (k : Fin 22), (↑q)[↑k] = (↑s.accepted)[↑k]
      |
      Aeneas.Std.core.result.Result.Err
          (AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted n d) =>
        s.accepted_len ≠ 22#usize ∧ n = s.accepted_len ∧ d = 64#usize
      | Aeneas.Std.core.result.Result.Err a => False
theorem AspisR1.NJT_QLeaves.block_rank : ∀ (b : AspisR1.NJT_QBase.Bytes) (out : AspisR1.NJT_QBase.Words),
  AspisR1.NJT_QLeaves.RankCut b out → AspisR1QueryScanUnrolled.r0_transcript.block_rank b = Aeneas.Std.Result.ok out :=
fun b out native =>
  have eq := AspisR1.NJT_QLeaves.array_window out (AspisR1.NJT_QBase.rank b) native;
  Eq.mpr (id (congrArg (fun _a => AspisR1QueryScanUnrolled.r0_transcript.block_rank b = Aeneas.Std.Result.ok _a) eq))
    (AspisR1.NJT_QBase.rank_source b)
theorem AspisR1.NJT_QLeaves.query_words : ∀ (b : AspisR1.NJT_QBase.Bytes) (out : AspisR1.NJT_QBase.Words),
  AspisR1.NJT_QLeaves.WordsCut b out → Query31ConcreteWordsDriverChain.actualQueryWords b = Aeneas.Std.Result.ok out :=
fun b out native =>
  have eq := AspisR1.NJT_QLeaves.array_window out (AspisR1.NJT_QBase.words b) native;
  Eq.mpr (id (congrArg (fun _a => Query31ConcreteWordsDriverChain.actualQueryWords b = Aeneas.Std.Result.ok _a) eq))
    (AspisR1.NJT_QBase.words_source b)
theorem AspisR1.NJT_QLeaves.finish : ∀ (s : AspisR1.NJT_QBase.State) (out : AspisR1.NJT_QBase.Finish),
  AspisR1.NJT_QLeaves.FinishCut s out →
    AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s = Aeneas.Std.Result.ok out :=
fun s out native =>
  let ⟨left✝, right✝⟩ := native
  let ⟨left✝¹, native⟩ := right✝
  have eq :=
    Aeneas.Std.core.result.Result.casesOn (motive := fun t => out = t → out = AspisR1.NJT_QBase.finish s) out
      (fun q h =>
        Eq.ndrec (motive := fun out =>
          (match out with
            | Aeneas.Std.core.result.Result.Ok q =>
              s.accepted_len = 22#usize ∧ ∀ (k : Fin 22), (↑q)[↑k] = (↑s.accepted)[↑k]
            |
            Aeneas.Std.core.result.Result.Err
                (AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted n d) =>
              s.accepted_len ≠ 22#usize ∧ n = s.accepted_len ∧ d = 64#usize
            | Aeneas.Std.core.result.Result.Err a => False) →
            out = AspisR1.NJT_QBase.finish s)
          (fun native =>
            let ⟨full, cells⟩ := native
            have arr := AspisR1.NJT_QLeaves.array_window q s.accepted cells;
            of_eq_true
              (Eq.trans
                (congr (congrArg Eq (congrArg Aeneas.Std.core.result.Result.Ok arr))
                  (Eq.trans
                    (ite_congr (Eq.trans (congrFun' (congrArg Eq full) 22#usize) (eq_self 22#usize))
                      (fun a => Eq.refl (Aeneas.Std.core.result.Result.Ok s.accepted)) fun a =>
                      congrArg Aeneas.Std.core.result.Result.Err
                        (congrFun'
                          (congrArg AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted
                            full)
                          64#usize))
                    (if_true (Aeneas.Std.core.result.Result.Ok s.accepted)
                      (Aeneas.Std.core.result.Result.Err
                        (AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted 22#usize
                          64#usize)))))
                (eq_self (Aeneas.Std.core.result.Result.Ok s.accepted))))
          (Eq.symm h) native)
      (fun error h =>
        Eq.ndrec (motive := fun out =>
          (match out with
            | Aeneas.Std.core.result.Result.Ok q =>
              s.accepted_len = 22#usize ∧ ∀ (k : Fin 22), (↑q)[↑k] = (↑s.accepted)[↑k]
            |
            Aeneas.Std.core.result.Result.Err
                (AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted n d) =>
              s.accepted_len ≠ 22#usize ∧ n = s.accepted_len ∧ d = 64#usize
            | Aeneas.Std.core.result.Result.Err a => False) →
            out = AspisR1.NJT_QBase.finish s)
          (fun native =>
            AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.casesOn (motive := fun t =>
              error = t → Aeneas.Std.core.result.Result.Err error = AspisR1.NJT_QBase.finish s) error
              (fun n h =>
                Eq.ndrec (motive := fun error =>
                  (match Aeneas.Std.core.result.Result.Err error with
                    | Aeneas.Std.core.result.Result.Ok q =>
                      s.accepted_len = 22#usize ∧ ∀ (k : Fin 22), (↑q)[↑k] = (↑s.accepted)[↑k]
                    |
                    Aeneas.Std.core.result.Result.Err
                        (AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted n d) =>
                      s.accepted_len ≠ 22#usize ∧ n = s.accepted_len ∧ d = 64#usize
                    | Aeneas.Std.core.result.Result.Err a => False) →
                    Aeneas.Std.core.result.Result.Err error = AspisR1.NJT_QBase.finish s)
                  (fun native => False.elim native) (Eq.symm h) native)
              (fun n b h =>
                Eq.ndrec (motive := fun error =>
                  (match Aeneas.Std.core.result.Result.Err error with
                    | Aeneas.Std.core.result.Result.Ok q =>
                      s.accepted_len = 22#usize ∧ ∀ (k : Fin 22), (↑q)[↑k] = (↑s.accepted)[↑k]
                    |
                    Aeneas.Std.core.result.Result.Err
                        (AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted n d) =>
                      s.accepted_len ≠ 22#usize ∧ n = s.accepted_len ∧ d = 64#usize
                    | Aeneas.Std.core.result.Result.Err a => False) →
                    Aeneas.Std.core.result.Result.Err error = AspisR1.NJT_QBase.finish s)
                  (fun native => False.elim native) (Eq.symm h) native)
              (fun n d h =>
                Eq.ndrec (motive := fun error =>
                  (match Aeneas.Std.core.result.Result.Err error with
                    | Aeneas.Std.core.result.Result.Ok q =>
                      s.accepted_len = 22#usize ∧ ∀ (k : Fin 22), (↑q)[↑k] = (↑s.accepted)[↑k]
                    |
                    Aeneas.Std.core.result.Result.Err
                        (AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted n d) =>
                      s.accepted_len ≠ 22#usize ∧ n = s.accepted_len ∧ d = 64#usize
                    | Aeneas.Std.core.result.Result.Err a => False) →
                    Aeneas.Std.core.result.Result.Err error = AspisR1.NJT_QBase.finish s)
                  (fun native =>
                    let ⟨notfull, right✝¹⟩ := native
                    let ⟨hn, hd⟩ := right✝¹
                    of_eq_true
                      (Eq.trans
                        (congr
                          (congrArg Eq
                            (congrArg Aeneas.Std.core.result.Result.Err
                              (congr
                                (congrArg
                                  AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted hn)
                                hd)))
                          (Eq.trans
                            (ite_congr (eq_false notfull)
                              (fun a => Eq.refl (Aeneas.Std.core.result.Result.Ok s.accepted)) fun a =>
                              Eq.refl
                                (Aeneas.Std.core.result.Result.Err
                                  (AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted
                                    s.accepted_len 64#usize)))
                            (if_false (Aeneas.Std.core.result.Result.Ok s.accepted)
                              (Aeneas.Std.core.result.Result.Err
                                (AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted
                                  s.accepted_len 64#usize)))))
                        (eq_self
                          (Aeneas.Std.core.result.Result.Err
                            (AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.DrawLimitExhausted
                              s.accepted_len 64#usize)))))
                  (Eq.symm h) native)
              (Eq.refl error))
          (Eq.symm h) native)
      (Eq.refl out);
  Eq.mpr
    (id
      (congrArg
        (fun _a => AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s = Aeneas.Std.Result.ok _a) eq))
    (AspisR1.NJT_QBase.finish_source s)
@[reducible] def AspisR1.NJT_QScan.Native : Type :=
AspisR1.NJT_QBase.State → Aeneas.Std.U32 → Bool → AspisR1.NJT_QScan.WordPost
def AspisR1.NJT_QScan.Cut : AspisR1.NJT_QScan.Native → Prop :=
fun native =>
  ∀ (s : AspisR1.NJT_QBase.State) (x : Aeneas.Std.U32) (reply : Bool),
    Query31ExplicitListLoop.validState s →
      ∀ (j : Fin 22),
        AspisR1.NHB_Observation.observe (native s x reply).state x 1 (native s x reply).stop j =
          AspisR1.NHK_WordAssociation.G s x 0 reply j
def AspisR1.NJT_QDomains.Domain : AspisR1.NJT_QBase.State → Prop :=
fun s => Query31ExplicitListLoop.validState s ∧ AspisR1.NHB_Canonical.State s ∧ AspisR1.NHB_Inactive.State s
theorem AspisR1.NJT_QReached.scan : ∀ (native : AspisR1.NJT_QScan.Native),
  AspisR1.NJT_QScan.Cut native →
    ∀ (priorBlocks : List AspisR1.NJT_QBase.Bytes) (block : AspisR1.NJT_QBase.Bytes),
      have before := AspisR1.NJT_QReached.carry native priorBlocks AspisR1.NGQ_SamplerPacket.initial;
      Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords before block =
          Aeneas.Std.Result.ok
            (Query31ExplicitListLoop.optionStop
                (AspisR1.NJT_QScan.run native (↑(AspisR1.NJT_QBase.words block)) before).2,
              (AspisR1.NJT_QScan.run native (↑(AspisR1.NJT_QBase.words block)) before).1) ∧
        AspisR1.NJT_QDomains.Domain before ∧
          AspisR1.NJT_QDomains.Domain (AspisR1.NJT_QScan.run native (↑(AspisR1.NJT_QBase.words block)) before).1 :=
fun native cut priorBlocks block =>
  have domain :=
    AspisR1.NJT_QReached.carry_domain native cut priorBlocks AspisR1.NGQ_SamplerPacket.initial
      AspisR1.NJT_QDomains.initial;
  ⟨AspisR1.NJT_QScan.scan native cut (AspisR1.NJT_QReached.carry native priorBlocks AspisR1.NGQ_SamplerPacket.initial)
      domain.left block,
    ⟨domain,
      AspisR1.NJT_QDomains.scan_preserved native cut block
        (AspisR1.NJT_QReached.carry native priorBlocks AspisR1.NGQ_SamplerPacket.initial) domain⟩⟩
theorem AspisR1.NJT_QPairs.reference : ∀ (native : AspisR1.NJT_QScan.Native),
  AspisR1.NJT_QScan.Cut native →
    ∀ (blocks advances : AspisR1.NJT_QPairs.Blocks),
      AspisR1Query31Transcript.queries_from_pairs_with_scan AspisR1.NGQ_SamplerPacket.Scan
          AspisR1.NGQ_SamplerPacket.initial blocks advances =
        AspisR1.NGQ_SamplerDriver.walk (AspisR1.NJT_QPairs.nativeScan native) advances 7#usize
          ((↑blocks).zip [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize])
          AspisR1.NGQ_SamplerPacket.initial :=
fun native cut blocks advances =>
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          _a =
            AspisR1.NGQ_SamplerDriver.walk (AspisR1.NJT_QPairs.nativeScan native) advances 7#usize
              ((↑blocks).zip [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize])
              AspisR1.NGQ_SamplerPacket.initial)
        (AspisR1.NGQ_SamplerDriver.source AspisR1.NGQ_SamplerPacket.Scan AspisR1.NGQ_SamplerPacket.initial blocks
          advances)))
    (AspisR1.NJT_QPairs.walk_source native cut advances 7#usize
      ((↑blocks).zip [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize])
      AspisR1.NGQ_SamplerPacket.initial AspisR1.NJT_QDomains.initial)
theorem AspisR1.NJT_QClaimsCanonical.claims : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix),
  AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok pre) →
    ∃ record,
      (AspisR1PublicPreparation.PrefixAdapter.fromOld pre).validated_record 25#u8 =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok record) ∧
        record.row = 25#u8 ∧
          ∀ (p off : Aeneas.Std.Usize),
            ↑p < 3 →
              ↑off = ↑p * 29 →
                ∃ out,
                  AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain 29#usize record off =
                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok out) :=
fun bytes pre parsed =>
  let idx := ⟨25, of_decide_eq_true (id (Eq.refl true))⟩;
  let frame := AspisR1.FJb_TailCell.cell pre.records idx;
  have recordLength := pre.records.property;
  have rowLength := rfl;
  have pairMember :=
    have bound :=
      Eq.mpr (id (congrArg (LT.lt 25) (Eq.trans List.length_zip (congr (congrArg min rowLength) recordLength))))
        (of_decide_eq_true (id (Eq.refl true)));
    have mem := List.mem_of_getElem List.getElem_zip;
    Eq.mpr
      (id
        (congrArg (Membership.mem (AspisR1.ExtractedPrefixTrace.rowOrder.zip ↑pre.records))
          (congrArg (Prod.mk 25#u8) (AspisR1.FJb_TailCell.cell.eq_1 pre.records idx))))
      (Eq.mp
        (congrArg (Membership.mem (AspisR1.ExtractedPrefixTrace.rowOrder.zip ↑pre.records))
          (congrFun'
            (congrArg Prod.mk
              (have this := Eq.refl AspisR1.ExtractedPrefixTrace.rowOrder[25];
              this))
            (↑pre.records)[25]))
        mem);
  let ⟨payload, recordParsed⟩ :=
    AspisR1.ExtractedPrefixParse.parse_record_of_success bytes pre parsed 25#u8 frame pairMember
  have strict :=
    AspisR1.NJT_QClaimsCanonical.strict_frame 25#u8 frame payload (of_decide_eq_true (id (Eq.refl true))) recordParsed;
  let ⟨record, h✝⟩ := AspisR1.NIX_ProducerInstall.lookup pre 25#u8 (of_decide_eq_true (id (Eq.refl true)))
  let ⟨getter, right✝⟩ := h✝
  let ⟨tag, same⟩ := right✝
  have equalFrame := same;
  have framed :=
    Eq.mpr (id (congrArg (fun _a => (↑_a).length = 3717) same))
      (AspisR1.NIX_PredecessorFrames.aggregate bytes pre parsed idx);
  Exists.intro record
    ⟨getter,
      ⟨tag, fun p off live offset =>
        AspisR1.NJT_QClaimsCanonical.decode record p off (congrArg Aeneas.Std.UScalar.val tag) live offset framed
          (Eq.mpr
            (id
              (forall_congr fun chunk =>
                implies_congr
                  (congrFun'
                    (congrArg Membership.mem
                      (congrArg Prod.fst
                        (Aeneas.Std.List.toChunksExact.congr_simp 32 32 (Eq.refl 32)
                          (of_decide_eq_true (id (Eq.refl true))) (List.drop 5 ↑record.framed) (List.drop 5 ↑frame)
                          (congrArg (List.drop 5) (congrArg Subtype.val equalFrame)))))
                    chunk)
                  (Eq.refl (AspisR1.ExtractedPrefixStrictPayload.StrictLowChunk chunk))))
            strict)⟩⟩

```
