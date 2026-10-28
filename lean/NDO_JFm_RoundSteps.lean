import NDO_JFm_Q15Source
import NDO_JFm_PartialAlpha
import NDO_JFm_Result
import NDO_JFr_RecordsAt
import NDO_JFm_Q16Source
import NDO_JFm_Q17Source
import NDO_JFm_Q18Source
import NDO_JFm_Q19Source
import NDO_JFm_Q20Source
import NDO_JFm_Q21Source
import NDO_JFm_Q22Source
import NDO_JFm_Q23Source
import NDO_JFm_Q24Source
set_option autoImplicit false
namespace AspisR1.JFm_Round00
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data00.running) (genToMain JFr_Data00.running)=ok false := by rfl
#print axioms comparison

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a00 (genToMain JFr_Data00.running) 0#usize=
      ok (.Ok (genToMain JFr_Data00.output,JFm_PartialAlpha.a01,
        (⟨encodeState JFm_Q15Source.ratchet,hash,16#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 15#u8 (by change 15<27;omega) JFw_NativeRow15.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨0,by omega⟩
  have sameRecord : vr=(⟨15#u8,JFw_NativeRow15.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨15#u8,JFw_NativeRow15.record⟩ 0#usize=ok (.Ok JFr_Round00.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q15Source.semantic D hash
  have same : q=JFm_Coordinates.value15 := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q15Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 0#usize=ok 15#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 0#usize) (by scalar_tac))
    have sameV : v=15#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round00.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update00,JFm_PartialAlpha.value00]

#print axioms source
end AspisR1.JFm_Round00
set_option autoImplicit false
namespace AspisR1.JFm_Round01
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data01.running) (genToMain JFr_Data01.running)=ok false := by rfl
#print axioms comparison

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q15Source.ratchet,hash,16#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a01 (genToMain JFr_Data01.running) 1#usize=
      ok (.Ok (genToMain JFr_Data01.output,JFm_PartialAlpha.a02,
        (⟨encodeState JFm_Q16Source.ratchet,hash,17#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 16#u8 (by change 16<27;omega) JFw_NativeRow16.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨1,by omega⟩
  have sameRecord : vr=(⟨16#u8,JFw_NativeRow16.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨16#u8,JFw_NativeRow16.record⟩ 0#usize=ok (.Ok JFr_Round01.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q16Source.semantic D hash
  have same : q=JFm_Coordinates.value16 := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q16Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 1#usize=ok 16#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 1#usize) (by scalar_tac))
    have sameV : v=16#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round01.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update01,JFm_PartialAlpha.value01]

#print axioms source
end AspisR1.JFm_Round01
set_option autoImplicit false
namespace AspisR1.JFm_Round02
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data02.running) (genToMain JFr_Data02.running)=ok false := by rfl
#print axioms comparison

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q16Source.ratchet,hash,17#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a02 (genToMain JFr_Data02.running) 2#usize=
      ok (.Ok (genToMain JFr_Data02.output,JFm_PartialAlpha.a03,
        (⟨encodeState JFm_Q17Source.ratchet,hash,18#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 17#u8 (by change 17<27;omega) JFw_NativeRow17.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨2,by omega⟩
  have sameRecord : vr=(⟨17#u8,JFw_NativeRow17.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨17#u8,JFw_NativeRow17.record⟩ 0#usize=ok (.Ok JFr_Round02.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q17Source.semantic D hash
  have same : q=JFm_Coordinates.value17 := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q17Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 2#usize=ok 17#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 2#usize) (by scalar_tac))
    have sameV : v=17#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round02.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update02,JFm_PartialAlpha.value02]

#print axioms source
end AspisR1.JFm_Round02
set_option autoImplicit false
namespace AspisR1.JFm_Round03
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data03.running) (genToMain JFr_Data03.running)=ok false := by rfl
#print axioms comparison

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q17Source.ratchet,hash,18#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a03 (genToMain JFr_Data03.running) 3#usize=
      ok (.Ok (genToMain JFr_Data03.output,JFm_PartialAlpha.a04,
        (⟨encodeState JFm_Q18Source.ratchet,hash,19#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 18#u8 (by change 18<27;omega) JFw_NativeRow18.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨3,by omega⟩
  have sameRecord : vr=(⟨18#u8,JFw_NativeRow18.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨18#u8,JFw_NativeRow18.record⟩ 0#usize=ok (.Ok JFr_Round03.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q18Source.semantic D hash
  have same : q=JFm_Coordinates.value18 := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q18Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 3#usize=ok 18#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 3#usize) (by scalar_tac))
    have sameV : v=18#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round03.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update03,JFm_PartialAlpha.value03]

#print axioms source
end AspisR1.JFm_Round03
set_option autoImplicit false
namespace AspisR1.JFm_Round04
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data04.running) (genToMain JFr_Data04.running)=ok false := by rfl
#print axioms comparison

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q18Source.ratchet,hash,19#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a04 (genToMain JFr_Data04.running) 4#usize=
      ok (.Ok (genToMain JFr_Data04.output,JFm_PartialAlpha.a05,
        (⟨encodeState JFm_Q19Source.ratchet,hash,20#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 19#u8 (by change 19<27;omega) JFw_NativeRow19.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨4,by omega⟩
  have sameRecord : vr=(⟨19#u8,JFw_NativeRow19.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨19#u8,JFw_NativeRow19.record⟩ 0#usize=ok (.Ok JFr_Round04.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q19Source.semantic D hash
  have same : q=JFm_Coordinates.value19 := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q19Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 4#usize=ok 19#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 4#usize) (by scalar_tac))
    have sameV : v=19#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round04.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update04,JFm_PartialAlpha.value04]

#print axioms source
end AspisR1.JFm_Round04
set_option autoImplicit false
namespace AspisR1.JFm_Round05
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data05.running) (genToMain JFr_Data05.running)=ok false := by rfl
#print axioms comparison

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q19Source.ratchet,hash,20#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a05 (genToMain JFr_Data05.running) 5#usize=
      ok (.Ok (genToMain JFr_Data05.output,JFm_PartialAlpha.a06,
        (⟨encodeState JFm_Q20Source.ratchet,hash,21#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 20#u8 (by change 20<27;omega) JFw_NativeRow20.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨5,by omega⟩
  have sameRecord : vr=(⟨20#u8,JFw_NativeRow20.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨20#u8,JFw_NativeRow20.record⟩ 0#usize=ok (.Ok JFr_Round05.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q20Source.semantic D hash
  have same : q=JFm_Coordinates.value20 := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q20Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 5#usize=ok 20#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 5#usize) (by scalar_tac))
    have sameV : v=20#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round05.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update05,JFm_PartialAlpha.value05]

#print axioms source
end AspisR1.JFm_Round05
set_option autoImplicit false
namespace AspisR1.JFm_Round06
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data06.running) (genToMain JFr_Data06.running)=ok false := by rfl
#print axioms comparison

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q20Source.ratchet,hash,21#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a06 (genToMain JFr_Data06.running) 6#usize=
      ok (.Ok (genToMain JFr_Data06.output,JFm_PartialAlpha.a07,
        (⟨encodeState JFm_Q21Source.ratchet,hash,22#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 21#u8 (by change 21<27;omega) JFw_NativeRow21.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨6,by omega⟩
  have sameRecord : vr=(⟨21#u8,JFw_NativeRow21.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨21#u8,JFw_NativeRow21.record⟩ 0#usize=ok (.Ok JFr_Round06.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q21Source.semantic D hash
  have same : q=JFm_Coordinates.value21 := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q21Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 6#usize=ok 21#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 6#usize) (by scalar_tac))
    have sameV : v=21#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round06.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update06,JFm_PartialAlpha.value06]

#print axioms source
end AspisR1.JFm_Round06
set_option autoImplicit false
namespace AspisR1.JFm_Round07
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data07.running) (genToMain JFr_Data07.running)=ok false := by rfl
#print axioms comparison

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q21Source.ratchet,hash,22#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a07 (genToMain JFr_Data07.running) 7#usize=
      ok (.Ok (genToMain JFr_Data07.output,JFm_PartialAlpha.a08,
        (⟨encodeState JFm_Q22Source.ratchet,hash,23#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 22#u8 (by change 22<27;omega) JFw_NativeRow22.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨7,by omega⟩
  have sameRecord : vr=(⟨22#u8,JFw_NativeRow22.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨22#u8,JFw_NativeRow22.record⟩ 0#usize=ok (.Ok JFr_Round07.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q22Source.semantic D hash
  have same : q=JFm_Coordinates.value22 := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q22Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 7#usize=ok 22#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 7#usize) (by scalar_tac))
    have sameV : v=22#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round07.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update07,JFm_PartialAlpha.value07]

#print axioms source
end AspisR1.JFm_Round07
set_option autoImplicit false
namespace AspisR1.JFm_Round08
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data08.running) (genToMain JFr_Data08.running)=ok false := by rfl
#print axioms comparison

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q22Source.ratchet,hash,23#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a08 (genToMain JFr_Data08.running) 8#usize=
      ok (.Ok (genToMain JFr_Data08.output,JFm_PartialAlpha.a09,
        (⟨encodeState JFm_Q23Source.ratchet,hash,24#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 23#u8 (by change 23<27;omega) JFw_NativeRow23.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨8,by omega⟩
  have sameRecord : vr=(⟨23#u8,JFw_NativeRow23.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨23#u8,JFw_NativeRow23.record⟩ 0#usize=ok (.Ok JFr_Round08.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q23Source.semantic D hash
  have same : q=JFm_Coordinates.value23 := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q23Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 8#usize=ok 23#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 8#usize) (by scalar_tac))
    have sameV : v=23#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round08.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update08,JFm_PartialAlpha.value08]

#print axioms source
end AspisR1.JFm_Round08
set_option autoImplicit false
namespace AspisR1.JFm_Round09
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data09.running) (genToMain JFr_Data09.running)=ok false := by rfl
#print axioms comparison

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q23Source.ratchet,hash,24#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a09 (genToMain JFr_Data09.running) 9#usize=
      ok (.Ok (genToMain JFr_Data09.output,JFm_PartialAlpha.a10,
        (⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 24#u8 (by change 24<27;omega) JFw_NativeRow24.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨9,by omega⟩
  have sameRecord : vr=(⟨24#u8,JFw_NativeRow24.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨24#u8,JFw_NativeRow24.record⟩ 0#usize=ok (.Ok JFr_Round09.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q24Source.semantic D hash
  have same : q=JFm_Coordinates.value24 := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q24Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 9#usize=ok 24#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 9#usize) (by scalar_tac))
    have sameV : v=24#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round09.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update09,JFm_PartialAlpha.value09]

#print axioms source
end AspisR1.JFm_Round09
