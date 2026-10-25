import Port6CK_Suffix
import Port6CK_Factor
import Port6CK_QueryFrame
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
open Port6CK_Ops (ops)
/-- Accepted current op18 body, on its SAME physical S2 bytes and returned
pair. Every sequential bound is derived from preceding reached reads. -/
theorem accepted (reserved : Bool) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (bytes : Slice U8) (length : bytes.val.length=1768)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (actual : Port4A_NativeReader.tail (ops reserved unwrap) bytes .S2 i4 end1 s6 a2=ok (.Ok (p,a))) :
    Port4A_NativeReader.tail (CheckpointBytes4Ops.ops reserved) bytes .S2 i4 end1 s6 a2=ok (.Ok (p,a)) := by
  rw [Port6CK_Factor.source] at actual ⊢
  unfold Port6CK_Factor.tail at actual ⊢
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
    change r0.at.val=(({ bytes := bytes, «at» := 80#usize } : verifier.Reader)).at.val+32 at cursor
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
    change r1.at.val=(r0).at.val+32 at cursor
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
    change r2.at.val=(r1).at.val+32 at cursor
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
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
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
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
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
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
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
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
            obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.e_success er2 er3 e3 bound called
            have cursor6 : er3.at.val=304 := by omega
            have backing6 : er3.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
            have oldBacking := backing6
            have room6 : er3.at.val+1432≤er3.bytes.val.length := by rw [cursor6,backing6,length]; decide
            have size6 : er3.bytes.val.length≤4096 := by rw [backing6,length]; decide
            obtain ⟨⟨value,rhoReader⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
            have bound : (er3).at.val+16≤(er3).bytes.val.length := by omega
            rw [show current unwrap er3=CheckpointBytes3Reader.readK er3 from Port5Q2_ReaderScalar.current_k unwrap unwrap_ok er3 bound size6] at called
            rw [called]
            simp only [bind_tc_ok,Aeneas.Std.uncurry]
            cases value with
            | Err e =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame] at actual
              cases actual
            | Ok rho =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success er3 rhoReader rho bound called
              have cursor7 : rhoReader.at.val=320 := by omega
              have backing7 : rhoReader.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing7
              have room7 : rhoReader.at.val+1416≤rhoReader.bytes.val.length := by rw [cursor7,backing7,length]; decide
              have size7 : rhoReader.bytes.val.length≤4096 := by rw [backing7,length]; decide
              rw [Port6CK_Queries.cps_bind] at actual ⊢
              obtain ⟨⟨queries,queriesReader⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [Port6CK_Queries.reference unwrap unwrap_ok rhoReader (by omega) size7] at called
              obtain ⟨cursor,backing⟩ := Port6CK_QueryFrame.reached rhoReader queriesReader queries (by omega) called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              have cursor8 : queriesReader.at.val=408 := by omega
              have backing8 : queriesReader.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing8
              have room8 : queriesReader.at.val+1328≤queriesReader.bytes.val.length := by rw [cursor8,backing8,length]; decide
              have size8 : queriesReader.bytes.val.length≤4096 := by rw [backing8,length]; decide
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
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                exact Port6CK_Suffix.accepted reserved unwrap unwrap_ok bytes length i4 end1
                  state root0 root1 e0 e1 e2 e3 rho queries queriesReader cursor8 backing8 p a actual

#print axioms accepted
end AspisR1.Port6CK_Tail
end
