import Port6CK_Roots
import Port6CK_Semantic
import Port6CK_Weights
import Port5Q2_ReaderValidate
import CheckpointBytes4SectionContents
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Tail
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port6CK_Semantic (Unwrap current)
/-- Current helper implementations at the retained parent's exact leaves.
The other leaves retain the existing Std/allocator/P6 interpretation. -/
def ops (reserved : Bool) (unwrap : Unwrap) : ResumeOps :=
  { CheckpointBytes4Ops.ops reserved with
    raw := fun N => Port5Q2_ReaderRaw.raw N (unwrap N)
    readK := current unwrap
    readE := Port5Q2_ReaderScalar.readE (fun N => Port5Q2_ReaderRaw.raw N (unwrap N))
      Port5Q2_ReaderScalar.decodeE
    readSemanticAlpha := Port5Q2_ReaderSemantic.semantic (current unwrap)
    validate := Port5Q2_ReaderValidate.validate
    readWeights := Port5Q2_ReaderWeights.weights (current unwrap) }

/-- Accepted current op18 body, on its SAME physical S2 bytes and returned
pair. Every sequential bound is derived from preceding reached reads. -/
theorem accepted (reserved : Bool) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (bytes : Slice U8) (length : bytes.val.length=1768)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (actual : Port4A_NativeReader.tail (ops reserved unwrap) bytes .S2 i4 end1 s6 a2=ok (.Ok (p,a))) :
    Port4A_NativeReader.tail (CheckpointBytes4Ops.ops reserved) bytes .S2 i4 end1 s6 a2=ok (.Ok (p,a)) := by
  unfold Port4A_NativeReader.tail at actual ⊢
  dsimp only [ops,CheckpointBytes4Ops.ops] at actual ⊢
  obtain ⟨bad,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  rw [called]
  simp only [bind_tc_ok]
  by_cases reject : bad=true
  · simp only [if_pos reject] at actual
    cases actual
  · simp only [if_neg reject] at actual ⊢
    obtain ⟨⟨state,r0⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
    have bound : (({ bytes := bytes, «at» := 80#usize } : verifier.Reader)).at.val+32≤(({ bytes := bytes, «at» := 80#usize } : verifier.Reader)).bytes.val.length := by
      first | change 80+32≤bytes.val.length; omega | omega
    rw [Port5Q2_ReaderRaw.reference 32#usize (unwrap _) (unwrap_ok _) ({ bytes := bytes, «at» := 80#usize } : verifier.Reader) bound
      (by first | change bytes.val.length≤4096; omega | exact size-1)] at called
    obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 32#usize ({ bytes := bytes, «at» := 80#usize } : verifier.Reader) r0 state bound called
    rw [called]
    simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
    change r0.at.val=80+32 at cursor
    change r0.bytes=bytes at backing
    have cursor0 : r0.at.val=112 := by omega
    have backing0 : r0.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
    have oldBacking := backing0
    have room0 : r0.at.val+1624≤r0.bytes.val.length := by rw [cursor0,backing0,length]; decide
    have size0 : r0.bytes.val.length≤4096 := by rw [backing0,length]; decide
    obtain ⟨⟨root0,r1⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
    have bound : (r0).at.val+32≤(r0).bytes.val.length := by
      first | change 80+32≤bytes.val.length; omega | omega
    rw [Port5Q2_ReaderRaw.reference 32#usize (unwrap _) (unwrap_ok _) r0 bound
      (by first | change bytes.val.length≤4096; omega | exact size0)] at called
    obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 32#usize r0 r1 root0 bound called
    rw [called]
    simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
    have cursor1 : r1.at.val=144 := by omega
    have backing1 : r1.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
    have oldBacking := backing1
    have room1 : r1.at.val+1592≤r1.bytes.val.length := by rw [cursor1,backing1,length]; decide
    have size1 : r1.bytes.val.length≤4096 := by rw [backing1,length]; decide
    obtain ⟨⟨root1,r2⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
    have bound : (r1).at.val+32≤(r1).bytes.val.length := by
      first | change 80+32≤bytes.val.length; omega | omega
    rw [Port5Q2_ReaderRaw.reference 32#usize (unwrap _) (unwrap_ok _) r1 bound
      (by first | change bytes.val.length≤4096; omega | exact size1)] at called
    obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 32#usize r1 r2 root1 bound called
    rw [called]
    simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
    have cursor2 : r2.at.val=176 := by omega
    have backing2 : r2.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
    have oldBacking := backing2
    have room2 : r2.at.val+1560≤r2.bytes.val.length := by rw [cursor2,backing2,length]; decide
    have size2 : r2.bytes.val.length≤4096 := by rw [backing2,length]; decide
    obtain ⟨⟨value,er0⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
    have bound : (r2).at.val+32≤(r2).bytes.val.length := by omega
    rw [Port5Q2_ReaderScalar.current_e unwrap unwrap_ok r2 bound size2] at called
    rw [called]
    simp only [bind_tc_ok,Aeneas.Std.uncurry]
    cases value with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at actual
      cases actual
    | Ok e0 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
      obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.e_success r2 er0 e0 bound called
      have cursor3 : er0.at.val=208 := by omega
      have backing3 : er0.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
      have oldBacking := backing3
      have room3 : er0.at.val+1528≤er0.bytes.val.length := by rw [cursor3,backing3,length]; decide
      have size3 : er0.bytes.val.length≤4096 := by rw [backing3,length]; decide
      obtain ⟨⟨value,er1⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
      have bound : (er0).at.val+32≤(er0).bytes.val.length := by omega
      rw [Port5Q2_ReaderScalar.current_e unwrap unwrap_ok er0 bound size3] at called
      rw [called]
      simp only [bind_tc_ok,Aeneas.Std.uncurry]
      cases value with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame] at actual
        cases actual
      | Ok e1 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
        obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.e_success er0 er1 e1 bound called
        have cursor4 : er1.at.val=240 := by omega
        have backing4 : er1.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
        have oldBacking := backing4
        have room4 : er1.at.val+1496≤er1.bytes.val.length := by rw [cursor4,backing4,length]; decide
        have size4 : er1.bytes.val.length≤4096 := by rw [backing4,length]; decide
        obtain ⟨⟨value,er2⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
        have bound : (er1).at.val+32≤(er1).bytes.val.length := by omega
        rw [Port5Q2_ReaderScalar.current_e unwrap unwrap_ok er1 bound size4] at called
        rw [called]
        simp only [bind_tc_ok,Aeneas.Std.uncurry]
        cases value with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame] at actual
          cases actual
        | Ok e2 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
          obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.e_success er1 er2 e2 bound called
          have cursor5 : er2.at.val=272 := by omega
          have backing5 : er2.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
          have oldBacking := backing5
          have room5 : er2.at.val+1464≤er2.bytes.val.length := by rw [cursor5,backing5,length]; decide
          have size5 : er2.bytes.val.length≤4096 := by rw [backing5,length]; decide
          obtain ⟨⟨value,er3⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
          have bound : (er2).at.val+32≤(er2).bytes.val.length := by omega
          rw [Port5Q2_ReaderScalar.current_e unwrap unwrap_ok er2 bound size5] at called
          rw [called]
          simp only [bind_tc_ok,Aeneas.Std.uncurry]
          cases value with
          | Err e =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame] at actual
            cases actual
          | Ok e3 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
            obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.e_success er2 er3 e3 bound called
            have cursor6 : er3.at.val=304 := by omega
            have backing6 : er3.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
            have oldBacking := backing6
            have room6 : er3.at.val+1432≤er3.bytes.val.length := by rw [cursor6,backing6,length]; decide
            have size6 : er3.bytes.val.length≤4096 := by rw [backing6,length]; decide
            obtain ⟨⟨value,rhoReader⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
            have bound : (er3).at.val+16≤(er3).bytes.val.length := by omega
            rw [Port5Q2_ReaderScalar.current_k unwrap unwrap_ok er3 bound size6] at called
            rw [called]
            simp only [bind_tc_ok,Aeneas.Std.uncurry]
            cases value with
            | Err e =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame] at actual
              cases actual
            | Ok rho =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
              obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success er3 rhoReader rho bound called
              have cursor7 : rhoReader.at.val=320 := by omega
              have backing7 : rhoReader.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing7
              have room7 : rhoReader.at.val+1416≤rhoReader.bytes.val.length := by rw [cursor7,backing7,length]; decide
              have size7 : rhoReader.bytes.val.length≤4096 := by rw [backing7,length]; decide
              obtain ⟨⟨queryBytes0,qr0⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (rhoReader).at.val+4≤(rhoReader).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) rhoReader bound
                (by first | change bytes.val.length≤4096; omega | exact size7)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize rhoReader qr0 queryBytes0 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor8 : qr0.at.val=324 := by omega
              have backing8 : qr0.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing8
              have room8 : qr0.at.val+1412≤qr0.bytes.val.length := by rw [cursor8,backing8,length]; decide
              have size8 : qr0.bytes.val.length≤4096 := by rw [backing8,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes1,qr1⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr0).at.val+4≤(qr0).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr0 bound
                (by first | change bytes.val.length≤4096; omega | exact size8)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr0 qr1 queryBytes1 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor9 : qr1.at.val=328 := by omega
              have backing9 : qr1.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing9
              have room9 : qr1.at.val+1408≤qr1.bytes.val.length := by rw [cursor9,backing9,length]; decide
              have size9 : qr1.bytes.val.length≤4096 := by rw [backing9,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes2,qr2⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr1).at.val+4≤(qr1).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr1 bound
                (by first | change bytes.val.length≤4096; omega | exact size9)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr1 qr2 queryBytes2 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor10 : qr2.at.val=332 := by omega
              have backing10 : qr2.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing10
              have room10 : qr2.at.val+1404≤qr2.bytes.val.length := by rw [cursor10,backing10,length]; decide
              have size10 : qr2.bytes.val.length≤4096 := by rw [backing10,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes3,qr3⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr2).at.val+4≤(qr2).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr2 bound
                (by first | change bytes.val.length≤4096; omega | exact size10)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr2 qr3 queryBytes3 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor11 : qr3.at.val=336 := by omega
              have backing11 : qr3.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing11
              have room11 : qr3.at.val+1400≤qr3.bytes.val.length := by rw [cursor11,backing11,length]; decide
              have size11 : qr3.bytes.val.length≤4096 := by rw [backing11,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes4,qr4⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr3).at.val+4≤(qr3).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr3 bound
                (by first | change bytes.val.length≤4096; omega | exact size11)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr3 qr4 queryBytes4 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor12 : qr4.at.val=340 := by omega
              have backing12 : qr4.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing12
              have room12 : qr4.at.val+1396≤qr4.bytes.val.length := by rw [cursor12,backing12,length]; decide
              have size12 : qr4.bytes.val.length≤4096 := by rw [backing12,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes5,qr5⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr4).at.val+4≤(qr4).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr4 bound
                (by first | change bytes.val.length≤4096; omega | exact size12)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr4 qr5 queryBytes5 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor13 : qr5.at.val=344 := by omega
              have backing13 : qr5.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing13
              have room13 : qr5.at.val+1392≤qr5.bytes.val.length := by rw [cursor13,backing13,length]; decide
              have size13 : qr5.bytes.val.length≤4096 := by rw [backing13,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes6,qr6⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr5).at.val+4≤(qr5).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr5 bound
                (by first | change bytes.val.length≤4096; omega | exact size13)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr5 qr6 queryBytes6 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor14 : qr6.at.val=348 := by omega
              have backing14 : qr6.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing14
              have room14 : qr6.at.val+1388≤qr6.bytes.val.length := by rw [cursor14,backing14,length]; decide
              have size14 : qr6.bytes.val.length≤4096 := by rw [backing14,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes7,qr7⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr6).at.val+4≤(qr6).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr6 bound
                (by first | change bytes.val.length≤4096; omega | exact size14)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr6 qr7 queryBytes7 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor15 : qr7.at.val=352 := by omega
              have backing15 : qr7.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing15
              have room15 : qr7.at.val+1384≤qr7.bytes.val.length := by rw [cursor15,backing15,length]; decide
              have size15 : qr7.bytes.val.length≤4096 := by rw [backing15,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes8,qr8⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr7).at.val+4≤(qr7).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr7 bound
                (by first | change bytes.val.length≤4096; omega | exact size15)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr7 qr8 queryBytes8 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor16 : qr8.at.val=356 := by omega
              have backing16 : qr8.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing16
              have room16 : qr8.at.val+1380≤qr8.bytes.val.length := by rw [cursor16,backing16,length]; decide
              have size16 : qr8.bytes.val.length≤4096 := by rw [backing16,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes9,qr9⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr8).at.val+4≤(qr8).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr8 bound
                (by first | change bytes.val.length≤4096; omega | exact size16)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr8 qr9 queryBytes9 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor17 : qr9.at.val=360 := by omega
              have backing17 : qr9.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing17
              have room17 : qr9.at.val+1376≤qr9.bytes.val.length := by rw [cursor17,backing17,length]; decide
              have size17 : qr9.bytes.val.length≤4096 := by rw [backing17,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes10,qr10⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr9).at.val+4≤(qr9).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr9 bound
                (by first | change bytes.val.length≤4096; omega | exact size17)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr9 qr10 queryBytes10 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor18 : qr10.at.val=364 := by omega
              have backing18 : qr10.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing18
              have room18 : qr10.at.val+1372≤qr10.bytes.val.length := by rw [cursor18,backing18,length]; decide
              have size18 : qr10.bytes.val.length≤4096 := by rw [backing18,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes11,qr11⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr10).at.val+4≤(qr10).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr10 bound
                (by first | change bytes.val.length≤4096; omega | exact size18)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr10 qr11 queryBytes11 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor19 : qr11.at.val=368 := by omega
              have backing19 : qr11.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing19
              have room19 : qr11.at.val+1368≤qr11.bytes.val.length := by rw [cursor19,backing19,length]; decide
              have size19 : qr11.bytes.val.length≤4096 := by rw [backing19,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes12,qr12⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr11).at.val+4≤(qr11).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr11 bound
                (by first | change bytes.val.length≤4096; omega | exact size19)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr11 qr12 queryBytes12 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor20 : qr12.at.val=372 := by omega
              have backing20 : qr12.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing20
              have room20 : qr12.at.val+1364≤qr12.bytes.val.length := by rw [cursor20,backing20,length]; decide
              have size20 : qr12.bytes.val.length≤4096 := by rw [backing20,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes13,qr13⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr12).at.val+4≤(qr12).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr12 bound
                (by first | change bytes.val.length≤4096; omega | exact size20)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr12 qr13 queryBytes13 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor21 : qr13.at.val=376 := by omega
              have backing21 : qr13.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing21
              have room21 : qr13.at.val+1360≤qr13.bytes.val.length := by rw [cursor21,backing21,length]; decide
              have size21 : qr13.bytes.val.length≤4096 := by rw [backing21,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes14,qr14⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr13).at.val+4≤(qr13).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr13 bound
                (by first | change bytes.val.length≤4096; omega | exact size21)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr13 qr14 queryBytes14 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor22 : qr14.at.val=380 := by omega
              have backing22 : qr14.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing22
              have room22 : qr14.at.val+1356≤qr14.bytes.val.length := by rw [cursor22,backing22,length]; decide
              have size22 : qr14.bytes.val.length≤4096 := by rw [backing22,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes15,qr15⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr14).at.val+4≤(qr14).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr14 bound
                (by first | change bytes.val.length≤4096; omega | exact size22)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr14 qr15 queryBytes15 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor23 : qr15.at.val=384 := by omega
              have backing23 : qr15.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing23
              have room23 : qr15.at.val+1352≤qr15.bytes.val.length := by rw [cursor23,backing23,length]; decide
              have size23 : qr15.bytes.val.length≤4096 := by rw [backing23,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes16,qr16⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr15).at.val+4≤(qr15).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr15 bound
                (by first | change bytes.val.length≤4096; omega | exact size23)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr15 qr16 queryBytes16 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor24 : qr16.at.val=388 := by omega
              have backing24 : qr16.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing24
              have room24 : qr16.at.val+1348≤qr16.bytes.val.length := by rw [cursor24,backing24,length]; decide
              have size24 : qr16.bytes.val.length≤4096 := by rw [backing24,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes17,qr17⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr16).at.val+4≤(qr16).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr16 bound
                (by first | change bytes.val.length≤4096; omega | exact size24)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr16 qr17 queryBytes17 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor25 : qr17.at.val=392 := by omega
              have backing25 : qr17.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing25
              have room25 : qr17.at.val+1344≤qr17.bytes.val.length := by rw [cursor25,backing25,length]; decide
              have size25 : qr17.bytes.val.length≤4096 := by rw [backing25,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes18,qr18⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr17).at.val+4≤(qr17).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr17 bound
                (by first | change bytes.val.length≤4096; omega | exact size25)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr17 qr18 queryBytes18 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor26 : qr18.at.val=396 := by omega
              have backing26 : qr18.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing26
              have room26 : qr18.at.val+1340≤qr18.bytes.val.length := by rw [cursor26,backing26,length]; decide
              have size26 : qr18.bytes.val.length≤4096 := by rw [backing26,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes19,qr19⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr18).at.val+4≤(qr18).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr18 bound
                (by first | change bytes.val.length≤4096; omega | exact size26)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr18 qr19 queryBytes19 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor27 : qr19.at.val=400 := by omega
              have backing27 : qr19.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing27
              have room27 : qr19.at.val+1336≤qr19.bytes.val.length := by rw [cursor27,backing27,length]; decide
              have size27 : qr19.bytes.val.length≤4096 := by rw [backing27,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes20,qr20⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr19).at.val+4≤(qr19).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr19 bound
                (by first | change bytes.val.length≤4096; omega | exact size27)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr19 qr20 queryBytes20 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor28 : qr20.at.val=404 := by omega
              have backing28 : qr20.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing28
              have room28 : qr20.at.val+1332≤qr20.bytes.val.length := by rw [cursor28,backing28,length]; decide
              have size28 : qr20.bytes.val.length≤4096 := by rw [backing28,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨⟨queryBytes21,qr21⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (qr20).at.val+4≤(qr20).bytes.val.length := by
                first | change 80+4≤bytes.val.length; omega | omega
              rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) qr20 bound
                (by first | change bytes.val.length≤4096; omega | exact size28)] at called
              obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize qr20 qr21 queryBytes21 bound called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor29 : qr21.at.val=408 := by omega
              have backing29 : qr21.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing29
              have room29 : qr21.at.val+1328≤qr21.bytes.val.length := by rw [cursor29,backing29,length]; decide
              have size29 : qr21.bytes.val.length≤4096 := by rw [backing29,length]; decide
              obtain ⟨query,queryRead,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [queryRead]
              simp only [bind_tc_ok]
              obtain ⟨checked,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [Port5Q2_ReaderValidate.reference] at called
              rw [called]
              simp only [bind_tc_ok]
              cases checked with
              | Err e =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame] at actual
                cases actual
              | Ok unit =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
                obtain ⟨semanticResult,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                rw [Port6CK_Semantic.reference unwrap unwrap_ok bytes qr21.at
                  (by rw [cursor29,length]; decide) (by omega)] at called
                rw [called]
                simp only [bind_tc_ok]
                cases semanticResult with
                | Err e =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame] at actual
                  cases actual
                | Ok pair =>
                  rcases pair with ⟨semanticAlpha,semanticEnd⟩
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
                  obtain ⟨model,decode,values,cursor⟩ := CheckpointBytes4SectionContents.semantic_contents bytes
                    qr21.at semanticEnd semanticAlpha (by rw [cursor29,length]; decide) called
                  have semanticCursor : semanticEnd.val=568 := by omega
                  let sr : verifier.Reader := { qr21 with «at» := semanticEnd }
                  have oldBacking : sr.bytes=bytes := backing29
                  have room30 : sr.at.val+1168≤sr.bytes.val.length := by change semanticEnd.val+1168≤qr21.bytes.val.length; rw [oldBacking,length]; omega
                  have size30 : sr.bytes.val.length≤4096 := by rw [oldBacking,length]; decide
                  change (do let pair ← current unwrap sr; _) = _ at actual
                  change (do let pair ← CheckpointBytes3Reader.readK sr; _) = _
                  obtain ⟨⟨value,cr0⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                  have bound : (sr).at.val+16≤(sr).bytes.val.length := by omega
                  rw [Port5Q2_ReaderScalar.current_k unwrap unwrap_ok sr bound size30] at called
                  rw [called]
                  simp only [bind_tc_ok,Aeneas.Std.uncurry]
                  cases value with
                  | Err e =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame] at actual
                    cases actual
                  | Ok coord0 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
                    obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success sr cr0 coord0 bound called
                    have cursor31 : cr0.at.val=584 := by omega
                    have backing31 : cr0.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
                    have oldBacking := backing31
                    have room31 : cr0.at.val+1152≤cr0.bytes.val.length := by rw [cursor31,backing31,length]; decide
                    have size31 : cr0.bytes.val.length≤4096 := by rw [backing31,length]; decide
                    obtain ⟨⟨value,cr1⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                    have bound : (cr0).at.val+16≤(cr0).bytes.val.length := by omega
                    rw [Port5Q2_ReaderScalar.current_k unwrap unwrap_ok cr0 bound size31] at called
                    rw [called]
                    simp only [bind_tc_ok,Aeneas.Std.uncurry]
                    cases value with
                    | Err e =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame] at actual
                      cases actual
                    | Ok coord1 =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
                      obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success cr0 cr1 coord1 bound called
                      have cursor32 : cr1.at.val=600 := by omega
                      have backing32 : cr1.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
                      have oldBacking := backing32
                      have room32 : cr1.at.val+1136≤cr1.bytes.val.length := by rw [cursor32,backing32,length]; decide
                      have size32 : cr1.bytes.val.length≤4096 := by rw [backing32,length]; decide
                      obtain ⟨⟨value,cr2⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                      have bound : (cr1).at.val+16≤(cr1).bytes.val.length := by omega
                      rw [Port5Q2_ReaderScalar.current_k unwrap unwrap_ok cr1 bound size32] at called
                      rw [called]
                      simp only [bind_tc_ok,Aeneas.Std.uncurry]
                      cases value with
                      | Err e =>
                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame] at actual
                        cases actual
                      | Ok coord2 =>
                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
                        obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success cr1 cr2 coord2 bound called
                        have cursor33 : cr2.at.val=616 := by omega
                        have backing33 : cr2.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
                        have oldBacking := backing33
                        have room33 : cr2.at.val+1120≤cr2.bytes.val.length := by rw [cursor33,backing33,length]; decide
                        have size33 : cr2.bytes.val.length≤4096 := by rw [backing33,length]; decide
                        obtain ⟨⟨value,cr3⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                        have bound : (cr2).at.val+16≤(cr2).bytes.val.length := by omega
                        rw [Port5Q2_ReaderScalar.current_k unwrap unwrap_ok cr2 bound size33] at called
                        rw [called]
                        simp only [bind_tc_ok,Aeneas.Std.uncurry]
                        cases value with
                        | Err e =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame] at actual
                          cases actual
                        | Ok coord3 =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
                          obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success cr2 cr3 coord3 bound called
                          have cursor34 : cr3.at.val=632 := by omega
                          have backing34 : cr3.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
                          have oldBacking := backing34
                          have room34 : cr3.at.val+1104≤cr3.bytes.val.length := by rw [cursor34,backing34,length]; decide
                          have size34 : cr3.bytes.val.length≤4096 := by rw [backing34,length]; decide
                          obtain ⟨⟨value,wr0⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                          have bound : (cr3).at.val+32≤(cr3).bytes.val.length := by omega
                          rw [Port5Q2_ReaderScalar.current_e unwrap unwrap_ok cr3 bound size34] at called
                          rw [called]
                          simp only [bind_tc_ok,Aeneas.Std.uncurry]
                          cases value with
                          | Err e =>
                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                              core.convert.FromSame] at actual
                            cases actual
                          | Ok wide0 =>
                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
                            obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.e_success cr3 wr0 wide0 bound called
                            have cursor35 : wr0.at.val=664 := by omega
                            have backing35 : wr0.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
                            have oldBacking := backing35
                            have room35 : wr0.at.val+1072≤wr0.bytes.val.length := by rw [cursor35,backing35,length]; decide
                            have size35 : wr0.bytes.val.length≤4096 := by rw [backing35,length]; decide
                            obtain ⟨⟨value,wr1⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                            have bound : (wr0).at.val+32≤(wr0).bytes.val.length := by omega
                            rw [Port5Q2_ReaderScalar.current_e unwrap unwrap_ok wr0 bound size35] at called
                            rw [called]
                            simp only [bind_tc_ok,Aeneas.Std.uncurry]
                            cases value with
                            | Err e =>
                              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                core.convert.FromSame] at actual
                              cases actual
                            | Ok wide1 =>
                              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
                              obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.e_success wr0 wr1 wide1 bound called
                              have cursor36 : wr1.at.val=696 := by omega
                              have backing36 : wr1.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
                              have oldBacking := backing36
                              have room36 : wr1.at.val+1040≤wr1.bytes.val.length := by rw [cursor36,backing36,length]; decide
                              have size36 : wr1.bytes.val.length≤4096 := by rw [backing36,length]; decide
                              obtain ⟨⟨value,powerReader⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                              have bound : (wr1).at.val+16≤(wr1).bytes.val.length := by omega
                              rw [Port5Q2_ReaderScalar.current_k unwrap unwrap_ok wr1 bound size36] at called
                              rw [called]
                              simp only [bind_tc_ok,Aeneas.Std.uncurry]
                              cases value with
                              | Err e =>
                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  core.convert.FromSame] at actual
                                cases actual
                              | Ok power =>
                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
                                obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success wr1 powerReader power bound called
                                have cursor37 : powerReader.at.val=712 := by omega
                                have backing37 : powerReader.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
                                have oldBacking := backing37
                                have room37 : powerReader.at.val+1024≤powerReader.bytes.val.length := by rw [cursor37,backing37,length]; decide
                                have size37 : powerReader.bytes.val.length≤4096 := by rw [backing37,length]; decide
                                obtain ⟨n,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                                have nEq : n=64#usize := Result.ok.inj called.symm
                                subst n
                                rw [called]
                                simp only [bind_tc_ok]
                                obtain ⟨zero,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                                rw [called]
                                simp only [bind_tc_ok]
                                obtain ⟨allocated,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                                rw [called]
                                simp only [bind_tc_ok]
                                cases allocated with
                                | Err e =>
                                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                    core.convert.FromSame] at actual
                                  cases actual
                                | Ok v =>
                                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at actual ⊢
                                  obtain ⟨weightsResult,weightCall,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                                  cases weightsResult with
                                  | Err e =>
                                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                      core.convert.FromSame] at actual
                                    cases actual
                                  | Ok pair =>
                                    rcases pair with ⟨weights,finish⟩
                                    have vSize : v.val.length=64 := by
                                      obtain ⟨_,contents⟩ := CheckpointBytes3Allocation.filled_success_content reserved 64#usize zero v called
                                      rw [contents,List.length_replicate]
                                      rfl
                                    have reference := Port6CK_Weights.accepted unwrap unwrap_ok bytes powerReader.at finish v weights
                                      (by rw [vSize,cursor37,length]; decide) (by omega) weightCall
                                    rw [reference]
                                    simp only [bind_tc_ok]
                                    exact actual

#print axioms accepted
end AspisR1.Port6CK_Tail
end
