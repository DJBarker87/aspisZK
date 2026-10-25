import Port6CK_Factor
import Port6CK_Ops
import CheckpointBytes4SectionContents
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Suffix
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port6CK_Semantic (Unwrap current)
open Port6CK_Ops (ops)
theorem accepted (reserved : Bool) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (bytes : Slice U8) (length : bytes.val.length=1768)
    (i4 : U8) (end1 : Usize) (state root0 root1 : Array U8 32#usize)
    (e0 e1 e2 e3 : aspis_core.field.wide_exact.WideExact) (rho : aspis_core.field.QM31)
    (queries : Array U32 22#usize) (queriesReader : verifier.Reader)
    (cursor8 : queriesReader.at.val=408) (backing8 : queriesReader.bytes=bytes)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (actual : Port6CK_Factor.suffix (ops reserved unwrap) bytes .S2 i4 end1 state root0 root1 e0 e1 e2 e3 rho queries queriesReader=ok (.Ok (p,a))) :
    Port6CK_Factor.suffix (CheckpointBytes4Ops.ops reserved) bytes .S2 i4 end1 state root0 root1 e0 e1 e2 e3 rho queries queriesReader=ok (.Ok (p,a)) := by
  unfold Port6CK_Factor.suffix at actual ⊢
  dsimp only [ops,CheckpointBytes4Ops.ops] at actual ⊢
  obtain ⟨semanticResult,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  rw [Port6CK_Semantic.reference unwrap unwrap_ok bytes queriesReader.at
    (by rw [cursor8,length]; decide) (by omega)] at called
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
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
    obtain ⟨model,decode,values,cursor⟩ := CheckpointBytes4SectionContents.semantic_contents bytes
      queriesReader.at semanticEnd semanticAlpha (by rw [cursor8,length]; decide) called
    have semanticCursor : semanticEnd.val=568 := by omega
    let sr : verifier.Reader := { queriesReader with «at» := semanticEnd }
    have oldBacking : sr.bytes=bytes := backing8
    have room9 : sr.at.val+1168≤sr.bytes.val.length := by change semanticEnd.val+1168≤queriesReader.bytes.val.length; rw [oldBacking,length]; omega
    have size9 : sr.bytes.val.length≤4096 := by rw [oldBacking,length]; decide
    change (do let pair ← current unwrap sr; _) = _ at actual
    change (do let pair ← CheckpointBytes3Reader.readK sr; _) = _
    obtain ⟨⟨value,cr0⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
    have bound : (sr).at.val+16≤(sr).bytes.val.length := by omega
    rw [show current unwrap sr=CheckpointBytes3Reader.readK sr from Port5Q2_ReaderScalar.current_k unwrap unwrap_ok sr bound size9] at called
    rw [called]
    simp only [bind_tc_ok,Aeneas.Std.uncurry]
    cases value with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at actual
      cases actual
    | Ok coord0 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
      obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success sr cr0 coord0 bound called
      have cursor10 : cr0.at.val=584 := by omega
      have backing10 : cr0.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
      have oldBacking := backing10
      have room10 : cr0.at.val+1152≤cr0.bytes.val.length := by rw [cursor10,backing10,length]; decide
      have size10 : cr0.bytes.val.length≤4096 := by rw [backing10,length]; decide
      obtain ⟨⟨value,cr1⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
      have bound : (cr0).at.val+16≤(cr0).bytes.val.length := by omega
      rw [show current unwrap cr0=CheckpointBytes3Reader.readK cr0 from Port5Q2_ReaderScalar.current_k unwrap unwrap_ok cr0 bound size10] at called
      rw [called]
      simp only [bind_tc_ok,Aeneas.Std.uncurry]
      cases value with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame] at actual
        cases actual
      | Ok coord1 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
        obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success cr0 cr1 coord1 bound called
        have cursor11 : cr1.at.val=600 := by omega
        have backing11 : cr1.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
        have oldBacking := backing11
        have room11 : cr1.at.val+1136≤cr1.bytes.val.length := by rw [cursor11,backing11,length]; decide
        have size11 : cr1.bytes.val.length≤4096 := by rw [backing11,length]; decide
        obtain ⟨⟨value,cr2⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
        have bound : (cr1).at.val+16≤(cr1).bytes.val.length := by omega
        rw [show current unwrap cr1=CheckpointBytes3Reader.readK cr1 from Port5Q2_ReaderScalar.current_k unwrap unwrap_ok cr1 bound size11] at called
        rw [called]
        simp only [bind_tc_ok,Aeneas.Std.uncurry]
        cases value with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame] at actual
          cases actual
        | Ok coord2 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
          obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success cr1 cr2 coord2 bound called
          have cursor12 : cr2.at.val=616 := by omega
          have backing12 : cr2.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
          have oldBacking := backing12
          have room12 : cr2.at.val+1120≤cr2.bytes.val.length := by rw [cursor12,backing12,length]; decide
          have size12 : cr2.bytes.val.length≤4096 := by rw [backing12,length]; decide
          obtain ⟨⟨value,cr3⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
          have bound : (cr2).at.val+16≤(cr2).bytes.val.length := by omega
          rw [show current unwrap cr2=CheckpointBytes3Reader.readK cr2 from Port5Q2_ReaderScalar.current_k unwrap unwrap_ok cr2 bound size12] at called
          rw [called]
          simp only [bind_tc_ok,Aeneas.Std.uncurry]
          cases value with
          | Err e =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame] at actual
            cases actual
          | Ok coord3 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
            obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success cr2 cr3 coord3 bound called
            have cursor13 : cr3.at.val=632 := by omega
            have backing13 : cr3.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
            have oldBacking := backing13
            have room13 : cr3.at.val+1104≤cr3.bytes.val.length := by rw [cursor13,backing13,length]; decide
            have size13 : cr3.bytes.val.length≤4096 := by rw [backing13,length]; decide
            obtain ⟨⟨value,wr0⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
            have bound : (cr3).at.val+32≤(cr3).bytes.val.length := by omega
            rw [Port5Q2_ReaderScalar.current_e unwrap unwrap_ok cr3 bound size13] at called
            rw [called]
            simp only [bind_tc_ok,Aeneas.Std.uncurry]
            cases value with
            | Err e =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame] at actual
              cases actual
            | Ok wide0 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.e_success cr3 wr0 wide0 bound called
              have cursor14 : wr0.at.val=664 := by omega
              have backing14 : wr0.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
              have oldBacking := backing14
              have room14 : wr0.at.val+1072≤wr0.bytes.val.length := by rw [cursor14,backing14,length]; decide
              have size14 : wr0.bytes.val.length≤4096 := by rw [backing14,length]; decide
              obtain ⟨⟨value,wr1⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              have bound : (wr0).at.val+32≤(wr0).bytes.val.length := by omega
              rw [Port5Q2_ReaderScalar.current_e unwrap unwrap_ok wr0 bound size14] at called
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry]
              cases value with
              | Err e =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame] at actual
                cases actual
              | Ok wide1 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.e_success wr0 wr1 wide1 bound called
                have cursor15 : wr1.at.val=696 := by omega
                have backing15 : wr1.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
                have oldBacking := backing15
                have room15 : wr1.at.val+1040≤wr1.bytes.val.length := by rw [cursor15,backing15,length]; decide
                have size15 : wr1.bytes.val.length≤4096 := by rw [backing15,length]; decide
                obtain ⟨⟨value,powerReader⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                have bound : (wr1).at.val+16≤(wr1).bytes.val.length := by omega
                rw [show current unwrap wr1=CheckpointBytes3Reader.readK wr1 from Port5Q2_ReaderScalar.current_k unwrap unwrap_ok wr1 bound size15] at called
                rw [called]
                simp only [bind_tc_ok,Aeneas.Std.uncurry]
                cases value with
                | Err e =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame] at actual
                  cases actual
                | Ok power =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success wr1 powerReader power bound called
                  have cursor16 : powerReader.at.val=712 := by omega
                  have backing16 : powerReader.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
                  have oldBacking := backing16
                  have room16 : powerReader.at.val+1024≤powerReader.bytes.val.length := by rw [cursor16,backing16,length]; decide
                  have size16 : powerReader.bytes.val.length≤4096 := by rw [backing16,length]; decide
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
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
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
                        (by rw [vSize,cursor16,length]; decide) (by omega) weightCall
                      rw [reference]
                      simp only [bind_tc_ok]
                      exact actual
#print axioms accepted
end AspisR1.Port6CK_Suffix
end
