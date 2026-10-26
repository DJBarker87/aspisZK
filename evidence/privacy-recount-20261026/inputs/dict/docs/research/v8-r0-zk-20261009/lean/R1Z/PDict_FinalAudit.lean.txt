import R1Z.PDict_CompletionAudit
import R1Z.PDict_CodecDictionary
import R1Z.PDict_CodecLength
import R1Z.PDict_CodecSource
import R1Z.PDict_ConstantsSource
import R1Z.PDict_CurrentCaller
import R1Z.PDict_CurrentRetention
import R1Z.PDict_FormatterDictionaryMap
import R1Z.PDict_FormatterIOMap
import R1Z.PDict_FormatterMatcherInventory
import R1Z.PDict_FormatterStoreMap
import R1Z.PDict_FormatterStorePath
import R1Z.PDict_FormatterTraitMap
import R1Z.PDict_FormatterTraitMap2
import R1Z.PDict_FormatterTransport0
import R1Z.PDict_FormatterTransport1
import R1Z.PDict_FormatterTypeEquiv
import R1Z.PDict_FormatterTypeMaps
import R1Z.PDict_LimbLayout
import R1Z.PDict_OwnedErrorCorrect
import R1Z.PDict_OwnedErrorDictionary
import R1Z.PDict_OwnedErrorObservation
import R1Z.PDict_OwnedErrorSource
import R1Z.PDict_OwnedErrorTransport
import R1Z.PDict_PureDictionary
import R1Z.PDict_PureEqCM31
import R1Z.PDict_PureSource
import R1Z.PDict_ReachCaller
import R1Z.PDict_ReachClient0
import R1Z.PDict_ReachClient1
import R1Z.PDict_ReachClient2
import R1Z.PDict_ReachErase22A
import R1Z.PDict_ReachErase22B
import R1Z.PDict_ReachErase23
import R1Z.PDict_ReachErase24
import R1Z.PDict_ReachErase25
import R1Z.PDict_ReachMaskedBody
import R1Z.PDict_ReachOpeningValues
import R1Z.PDict_ReachPublicationFrame
import R1Z.PDict_ReachQueryOpenings
import R1Z.PDict_ReachRetryComplete
import R1Z.PDict_ReachSemantics
import R1Z.PDict_ReserveFailure
import R1Z.PDict_ResultTransport
set_option autoImplicit false
namespace R1Z.PDict_FinalAudit
open Aeneas Aeneas.Std Result ProverRwFull PDict_OwnedErrorCorrect

/-- Map the error arm, preserving the successful Bool arm. -/
def eraseOwned : core.result.Result Bool Owned → core.result.Result Bool Kind
  | .Ok b => .Ok b
  | .Err e => .Err (decode e)
def embedOwned : core.result.Result Bool Kind → core.result.Result Bool Owned
  | .Ok b => .Ok b
  | .Err k => .Err (encode k)

def referenceCarrier : Owned ≃ Kind where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

theorem owned_result_roundtrip (r : core.result.Result Bool Owned) :
    embedOwned (eraseOwned r) = r := by
  cases r with
  | Ok b => rfl
  | Err e => cases e; rfl

/-- All success/error inputs of the actual extracted owned reference. Native
std.io.Error, File/world and whole-caller adequacy remain separate obligations. -/
theorem complete_owned_observation (r : core.result.Result Bool Owned) :
    PDict_OwnedErrorSource.owned_error_observe r =
    .ok (match eraseOwned r with
      | .Ok b => (⟨b,none⟩ : Observation)
      | .Err k => ⟨false,some k⟩) := by
  cases r <;> rfl

#print axioms referenceCarrier
#print axioms owned_result_roundtrip
#print axioms complete_owned_observation
end R1Z.PDict_FinalAudit

#print axioms PDict_CodecSource.aspis_core.field.P
#print axioms PDict_CodecSource.aspis_core.field.wide_exact.WideExact.BYTE_LEN
#print axioms PDict_CodecSource.aspis_core.field.wide_exact.WideExact.from_le_bytes
#print axioms PDict_CodecSource.aspis_core.field.wide_exact.WideExact.from_limbs
#print axioms PDict_CodecSource.aspis_core.field.wide_exact.WideExact.to_limbs
#print axioms PDict_ConstantsSource.aspis_r1_cost_probe.multiproof.LEAF_BITS
#print axioms PDict_ConstantsSource.aspis_r1_cost_probe.multiproof.MAX_BATCH
#print axioms PDict_ConstantsSource.aspis_r1_cost_probe.r1_wire.CLAIMS
#print axioms PDict_ConstantsSource.aspis_r1_cost_probe.r1_wire.DOMAIN
#print axioms PDict_ConstantsSource.aspis_r1_cost_probe.r1_wire.LANES
#print axioms PDict_ConstantsSource.aspis_r1_cost_probe.r1_wire.POINTS
#print axioms PDict_ConstantsSource.claims
#print axioms PDict_ConstantsSource.domain
#print axioms PDict_ConstantsSource.lanes
#print axioms PDict_ConstantsSource.leaf_bits
#print axioms PDict_ConstantsSource.max_batch
#print axioms PDict_OwnedErrorSource.core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq
#print axioms PDict_OwnedErrorSource.owned_error.owned_observe
#print axioms PDict_OwnedErrorSource.owned_error.owned_open_error
#print axioms PDict_OwnedErrorSource.owned_error_observe
#print axioms PDict_OwnedErrorSource.owned_error_open
#print axioms PDict_PureSource.aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint
#print axioms PDict_PureSource.aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
#print axioms PDict_PureSource.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq
#print axioms PDict_PureSource.aspis_core.field.CM31.new
#print axioms PDict_PureSource.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
#print axioms PDict_PureSource.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
#print axioms PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone
#print axioms PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact
#print axioms PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq
#print axioms PDict_PureSource.aspis_core.field.wide_exact.WideExact.impl.c0
#print axioms PDict_PureSource.aspis_core.field.wide_exact.WideExact.impl.c1
#print axioms R1Z.PDict_CodecDictionary.op49_installed
#print axioms R1Z.PDict_CodecDictionary.op50_installed
#print axioms R1Z.PDict_CodecDictionary.op51_retained
#print axioms R1Z.PDict_CodecLength.reject_length
#print axioms R1Z.PDict_CodecLength.selected_reject_length
#print axioms R1Z.PDict_CurrentCaller.caller_property
#print axioms R1Z.PDict_CurrentCaller.seven_field_caller
#print axioms R1Z.PDict_CurrentRetention.retain_0
#print axioms R1Z.PDict_CurrentRetention.retain_1
#print axioms R1Z.PDict_CurrentRetention.retain_10
#print axioms R1Z.PDict_CurrentRetention.retain_100
#print axioms R1Z.PDict_CurrentRetention.retain_101
#print axioms R1Z.PDict_CurrentRetention.retain_102
#print axioms R1Z.PDict_CurrentRetention.retain_103
#print axioms R1Z.PDict_CurrentRetention.retain_104
#print axioms R1Z.PDict_CurrentRetention.retain_105
#print axioms R1Z.PDict_CurrentRetention.retain_106
#print axioms R1Z.PDict_CurrentRetention.retain_107
#print axioms R1Z.PDict_CurrentRetention.retain_108
#print axioms R1Z.PDict_CurrentRetention.retain_109
#print axioms R1Z.PDict_CurrentRetention.retain_11
#print axioms R1Z.PDict_CurrentRetention.retain_110
#print axioms R1Z.PDict_CurrentRetention.retain_111
#print axioms R1Z.PDict_CurrentRetention.retain_112
#print axioms R1Z.PDict_CurrentRetention.retain_113
#print axioms R1Z.PDict_CurrentRetention.retain_114
#print axioms R1Z.PDict_CurrentRetention.retain_115
#print axioms R1Z.PDict_CurrentRetention.retain_116
#print axioms R1Z.PDict_CurrentRetention.retain_117
#print axioms R1Z.PDict_CurrentRetention.retain_118
#print axioms R1Z.PDict_CurrentRetention.retain_119
#print axioms R1Z.PDict_CurrentRetention.retain_12
#print axioms R1Z.PDict_CurrentRetention.retain_120
#print axioms R1Z.PDict_CurrentRetention.retain_121
#print axioms R1Z.PDict_CurrentRetention.retain_122
#print axioms R1Z.PDict_CurrentRetention.retain_123
#print axioms R1Z.PDict_CurrentRetention.retain_124
#print axioms R1Z.PDict_CurrentRetention.retain_125
#print axioms R1Z.PDict_CurrentRetention.retain_126
#print axioms R1Z.PDict_CurrentRetention.retain_127
#print axioms R1Z.PDict_CurrentRetention.retain_128
#print axioms R1Z.PDict_CurrentRetention.retain_129
#print axioms R1Z.PDict_CurrentRetention.retain_13
#print axioms R1Z.PDict_CurrentRetention.retain_130
#print axioms R1Z.PDict_CurrentRetention.retain_131
#print axioms R1Z.PDict_CurrentRetention.retain_132
#print axioms R1Z.PDict_CurrentRetention.retain_133
#print axioms R1Z.PDict_CurrentRetention.retain_134
#print axioms R1Z.PDict_CurrentRetention.retain_135
#print axioms R1Z.PDict_CurrentRetention.retain_136
#print axioms R1Z.PDict_CurrentRetention.retain_137
#print axioms R1Z.PDict_CurrentRetention.retain_138
#print axioms R1Z.PDict_CurrentRetention.retain_139
#print axioms R1Z.PDict_CurrentRetention.retain_14
#print axioms R1Z.PDict_CurrentRetention.retain_140
#print axioms R1Z.PDict_CurrentRetention.retain_141
#print axioms R1Z.PDict_CurrentRetention.retain_142
#print axioms R1Z.PDict_CurrentRetention.retain_143
#print axioms R1Z.PDict_CurrentRetention.retain_144
#print axioms R1Z.PDict_CurrentRetention.retain_145
#print axioms R1Z.PDict_CurrentRetention.retain_146
#print axioms R1Z.PDict_CurrentRetention.retain_147
#print axioms R1Z.PDict_CurrentRetention.retain_148
#print axioms R1Z.PDict_CurrentRetention.retain_149
#print axioms R1Z.PDict_CurrentRetention.retain_15
#print axioms R1Z.PDict_CurrentRetention.retain_150
#print axioms R1Z.PDict_CurrentRetention.retain_151
#print axioms R1Z.PDict_CurrentRetention.retain_152
#print axioms R1Z.PDict_CurrentRetention.retain_153
#print axioms R1Z.PDict_CurrentRetention.retain_154
#print axioms R1Z.PDict_CurrentRetention.retain_155
#print axioms R1Z.PDict_CurrentRetention.retain_156
#print axioms R1Z.PDict_CurrentRetention.retain_157
#print axioms R1Z.PDict_CurrentRetention.retain_158
#print axioms R1Z.PDict_CurrentRetention.retain_159
#print axioms R1Z.PDict_CurrentRetention.retain_16
#print axioms R1Z.PDict_CurrentRetention.retain_160
#print axioms R1Z.PDict_CurrentRetention.retain_161
#print axioms R1Z.PDict_CurrentRetention.retain_162
#print axioms R1Z.PDict_CurrentRetention.retain_163
#print axioms R1Z.PDict_CurrentRetention.retain_164
#print axioms R1Z.PDict_CurrentRetention.retain_165
#print axioms R1Z.PDict_CurrentRetention.retain_166
#print axioms R1Z.PDict_CurrentRetention.retain_167
#print axioms R1Z.PDict_CurrentRetention.retain_168
#print axioms R1Z.PDict_CurrentRetention.retain_169
#print axioms R1Z.PDict_CurrentRetention.retain_17
#print axioms R1Z.PDict_CurrentRetention.retain_170
#print axioms R1Z.PDict_CurrentRetention.retain_171
#print axioms R1Z.PDict_CurrentRetention.retain_172
#print axioms R1Z.PDict_CurrentRetention.retain_173
#print axioms R1Z.PDict_CurrentRetention.retain_174
#print axioms R1Z.PDict_CurrentRetention.retain_175
#print axioms R1Z.PDict_CurrentRetention.retain_176
#print axioms R1Z.PDict_CurrentRetention.retain_177
#print axioms R1Z.PDict_CurrentRetention.retain_178
#print axioms R1Z.PDict_CurrentRetention.retain_179
#print axioms R1Z.PDict_CurrentRetention.retain_18
#print axioms R1Z.PDict_CurrentRetention.retain_180
#print axioms R1Z.PDict_CurrentRetention.retain_181
#print axioms R1Z.PDict_CurrentRetention.retain_182
#print axioms R1Z.PDict_CurrentRetention.retain_183
#print axioms R1Z.PDict_CurrentRetention.retain_184
#print axioms R1Z.PDict_CurrentRetention.retain_185
#print axioms R1Z.PDict_CurrentRetention.retain_186
#print axioms R1Z.PDict_CurrentRetention.retain_187
#print axioms R1Z.PDict_CurrentRetention.retain_188
#print axioms R1Z.PDict_CurrentRetention.retain_189
#print axioms R1Z.PDict_CurrentRetention.retain_19
#print axioms R1Z.PDict_CurrentRetention.retain_190
#print axioms R1Z.PDict_CurrentRetention.retain_191
#print axioms R1Z.PDict_CurrentRetention.retain_192
#print axioms R1Z.PDict_CurrentRetention.retain_193
#print axioms R1Z.PDict_CurrentRetention.retain_194
#print axioms R1Z.PDict_CurrentRetention.retain_195
#print axioms R1Z.PDict_CurrentRetention.retain_196
#print axioms R1Z.PDict_CurrentRetention.retain_197
#print axioms R1Z.PDict_CurrentRetention.retain_198
#print axioms R1Z.PDict_CurrentRetention.retain_199
#print axioms R1Z.PDict_CurrentRetention.retain_2
#print axioms R1Z.PDict_CurrentRetention.retain_20
#print axioms R1Z.PDict_CurrentRetention.retain_200
#print axioms R1Z.PDict_CurrentRetention.retain_201
#print axioms R1Z.PDict_CurrentRetention.retain_202
#print axioms R1Z.PDict_CurrentRetention.retain_203
#print axioms R1Z.PDict_CurrentRetention.retain_204
#print axioms R1Z.PDict_CurrentRetention.retain_205
#print axioms R1Z.PDict_CurrentRetention.retain_206
#print axioms R1Z.PDict_CurrentRetention.retain_207
#print axioms R1Z.PDict_CurrentRetention.retain_208
#print axioms R1Z.PDict_CurrentRetention.retain_209
#print axioms R1Z.PDict_CurrentRetention.retain_21
#print axioms R1Z.PDict_CurrentRetention.retain_210
#print axioms R1Z.PDict_CurrentRetention.retain_211
#print axioms R1Z.PDict_CurrentRetention.retain_212
#print axioms R1Z.PDict_CurrentRetention.retain_213
#print axioms R1Z.PDict_CurrentRetention.retain_214
#print axioms R1Z.PDict_CurrentRetention.retain_215
#print axioms R1Z.PDict_CurrentRetention.retain_216
#print axioms R1Z.PDict_CurrentRetention.retain_217
#print axioms R1Z.PDict_CurrentRetention.retain_218
#print axioms R1Z.PDict_CurrentRetention.retain_219
#print axioms R1Z.PDict_CurrentRetention.retain_22
#print axioms R1Z.PDict_CurrentRetention.retain_220
#print axioms R1Z.PDict_CurrentRetention.retain_221
#print axioms R1Z.PDict_CurrentRetention.retain_222
#print axioms R1Z.PDict_CurrentRetention.retain_223
#print axioms R1Z.PDict_CurrentRetention.retain_224
#print axioms R1Z.PDict_CurrentRetention.retain_225
#print axioms R1Z.PDict_CurrentRetention.retain_226
#print axioms R1Z.PDict_CurrentRetention.retain_227
#print axioms R1Z.PDict_CurrentRetention.retain_228
#print axioms R1Z.PDict_CurrentRetention.retain_229
#print axioms R1Z.PDict_CurrentRetention.retain_23
#print axioms R1Z.PDict_CurrentRetention.retain_230
#print axioms R1Z.PDict_CurrentRetention.retain_231
#print axioms R1Z.PDict_CurrentRetention.retain_232
#print axioms R1Z.PDict_CurrentRetention.retain_233
#print axioms R1Z.PDict_CurrentRetention.retain_234
#print axioms R1Z.PDict_CurrentRetention.retain_237
#print axioms R1Z.PDict_CurrentRetention.retain_238
#print axioms R1Z.PDict_CurrentRetention.retain_24
#print axioms R1Z.PDict_CurrentRetention.retain_241
#print axioms R1Z.PDict_CurrentRetention.retain_242
#print axioms R1Z.PDict_CurrentRetention.retain_243
#print axioms R1Z.PDict_CurrentRetention.retain_244
#print axioms R1Z.PDict_CurrentRetention.retain_245
#print axioms R1Z.PDict_CurrentRetention.retain_246
#print axioms R1Z.PDict_CurrentRetention.retain_247
#print axioms R1Z.PDict_CurrentRetention.retain_248
#print axioms R1Z.PDict_CurrentRetention.retain_249
#print axioms R1Z.PDict_CurrentRetention.retain_25
#print axioms R1Z.PDict_CurrentRetention.retain_250
#print axioms R1Z.PDict_CurrentRetention.retain_251
#print axioms R1Z.PDict_CurrentRetention.retain_252
#print axioms R1Z.PDict_CurrentRetention.retain_253
#print axioms R1Z.PDict_CurrentRetention.retain_254
#print axioms R1Z.PDict_CurrentRetention.retain_255
#print axioms R1Z.PDict_CurrentRetention.retain_256
#print axioms R1Z.PDict_CurrentRetention.retain_257
#print axioms R1Z.PDict_CurrentRetention.retain_258
#print axioms R1Z.PDict_CurrentRetention.retain_259
#print axioms R1Z.PDict_CurrentRetention.retain_26
#print axioms R1Z.PDict_CurrentRetention.retain_261
#print axioms R1Z.PDict_CurrentRetention.retain_27
#print axioms R1Z.PDict_CurrentRetention.retain_28
#print axioms R1Z.PDict_CurrentRetention.retain_29
#print axioms R1Z.PDict_CurrentRetention.retain_3
#print axioms R1Z.PDict_CurrentRetention.retain_30
#print axioms R1Z.PDict_CurrentRetention.retain_31
#print axioms R1Z.PDict_CurrentRetention.retain_32
#print axioms R1Z.PDict_CurrentRetention.retain_33
#print axioms R1Z.PDict_CurrentRetention.retain_34
#print axioms R1Z.PDict_CurrentRetention.retain_35
#print axioms R1Z.PDict_CurrentRetention.retain_36
#print axioms R1Z.PDict_CurrentRetention.retain_38
#print axioms R1Z.PDict_CurrentRetention.retain_39
#print axioms R1Z.PDict_CurrentRetention.retain_4
#print axioms R1Z.PDict_CurrentRetention.retain_42
#print axioms R1Z.PDict_CurrentRetention.retain_45
#print axioms R1Z.PDict_CurrentRetention.retain_46
#print axioms R1Z.PDict_CurrentRetention.retain_47
#print axioms R1Z.PDict_CurrentRetention.retain_48
#print axioms R1Z.PDict_CurrentRetention.retain_5
#print axioms R1Z.PDict_CurrentRetention.retain_51
#print axioms R1Z.PDict_CurrentRetention.retain_52
#print axioms R1Z.PDict_CurrentRetention.retain_53
#print axioms R1Z.PDict_CurrentRetention.retain_54
#print axioms R1Z.PDict_CurrentRetention.retain_55
#print axioms R1Z.PDict_CurrentRetention.retain_56
#print axioms R1Z.PDict_CurrentRetention.retain_57
#print axioms R1Z.PDict_CurrentRetention.retain_58
#print axioms R1Z.PDict_CurrentRetention.retain_59
#print axioms R1Z.PDict_CurrentRetention.retain_6
#print axioms R1Z.PDict_CurrentRetention.retain_61
#print axioms R1Z.PDict_CurrentRetention.retain_62
#print axioms R1Z.PDict_CurrentRetention.retain_63
#print axioms R1Z.PDict_CurrentRetention.retain_64
#print axioms R1Z.PDict_CurrentRetention.retain_65
#print axioms R1Z.PDict_CurrentRetention.retain_66
#print axioms R1Z.PDict_CurrentRetention.retain_67
#print axioms R1Z.PDict_CurrentRetention.retain_68
#print axioms R1Z.PDict_CurrentRetention.retain_69
#print axioms R1Z.PDict_CurrentRetention.retain_7
#print axioms R1Z.PDict_CurrentRetention.retain_70
#print axioms R1Z.PDict_CurrentRetention.retain_71
#print axioms R1Z.PDict_CurrentRetention.retain_72
#print axioms R1Z.PDict_CurrentRetention.retain_73
#print axioms R1Z.PDict_CurrentRetention.retain_74
#print axioms R1Z.PDict_CurrentRetention.retain_75
#print axioms R1Z.PDict_CurrentRetention.retain_76
#print axioms R1Z.PDict_CurrentRetention.retain_77
#print axioms R1Z.PDict_CurrentRetention.retain_78
#print axioms R1Z.PDict_CurrentRetention.retain_79
#print axioms R1Z.PDict_CurrentRetention.retain_8
#print axioms R1Z.PDict_CurrentRetention.retain_80
#print axioms R1Z.PDict_CurrentRetention.retain_81
#print axioms R1Z.PDict_CurrentRetention.retain_82
#print axioms R1Z.PDict_CurrentRetention.retain_83
#print axioms R1Z.PDict_CurrentRetention.retain_84
#print axioms R1Z.PDict_CurrentRetention.retain_85
#print axioms R1Z.PDict_CurrentRetention.retain_86
#print axioms R1Z.PDict_CurrentRetention.retain_87
#print axioms R1Z.PDict_CurrentRetention.retain_88
#print axioms R1Z.PDict_CurrentRetention.retain_89
#print axioms R1Z.PDict_CurrentRetention.retain_9
#print axioms R1Z.PDict_CurrentRetention.retain_90
#print axioms R1Z.PDict_CurrentRetention.retain_91
#print axioms R1Z.PDict_CurrentRetention.retain_92
#print axioms R1Z.PDict_CurrentRetention.retain_93
#print axioms R1Z.PDict_CurrentRetention.retain_94
#print axioms R1Z.PDict_CurrentRetention.retain_95
#print axioms R1Z.PDict_CurrentRetention.retain_96
#print axioms R1Z.PDict_CurrentRetention.retain_97
#print axioms R1Z.PDict_CurrentRetention.retain_98
#print axioms R1Z.PDict_CurrentRetention.retain_99
#print axioms R1Z.PDict_FormatterDictionaryMap.formatter_erased
#print axioms R1Z.PDict_FormatterDictionaryMap.kind_retained
#print axioms R1Z.PDict_FormatterIOMap.io14
#print axioms R1Z.PDict_FormatterIOMap.io15
#print axioms R1Z.PDict_FormatterIOMap.io19
#print axioms R1Z.PDict_FormatterIOMap.io20
#print axioms R1Z.PDict_FormatterIOMap.io21
#print axioms R1Z.PDict_FormatterIOMap.io22
#print axioms R1Z.PDict_FormatterIOMap.io23
#print axioms R1Z.PDict_FormatterIOMap.io24
#print axioms R1Z.PDict_FormatterIOMap.io25
#print axioms R1Z.PDict_FormatterIOMap.io26
#print axioms R1Z.PDict_FormatterIOMap.io261
#print axioms R1Z.PDict_FormatterIOMap.io27
#print axioms R1Z.PDict_FormatterIOMap.io28
#print axioms R1Z.PDict_FormatterIOMap.io29
#print axioms R1Z.PDict_FormatterIOMap.io30
#print axioms R1Z.PDict_FormatterIOMap.io31
#print axioms R1Z.PDict_FormatterIOMap.sync_directory
#print axioms R1Z.PDict_FormatterStoreMap.reserve
#print axioms R1Z.PDict_FormatterStoreMap.store_roundtrip
#print axioms R1Z.PDict_FormatterStorePath.reservation_path
#print axioms R1Z.PDict_FormatterTraitMap.unBuffer
#print axioms R1Z.PDict_FormatterTraitMap.unBufferUser
#print axioms R1Z.PDict_FormatterTraitMap.unSealed
#print axioms R1Z.PDict_FormatterTraitMap.unUpdate
#print axioms R1Z.PDict_FormatterTraitMap.unVariable
#print axioms R1Z.PDict_FormatterTraitMap2.unFixed
#print axioms R1Z.PDict_FormatterTraitMap2.unFixedCore
#print axioms R1Z.PDict_FormatterTransport.lower_0
#print axioms R1Z.PDict_FormatterTransport.lower_1
#print axioms R1Z.PDict_FormatterTransport.lower_12
#print axioms R1Z.PDict_FormatterTransport.lower_13
#print axioms R1Z.PDict_FormatterTransport.lower_14
#print axioms R1Z.PDict_FormatterTransport.lower_15
#print axioms R1Z.PDict_FormatterTransport.lower_16
#print axioms R1Z.PDict_FormatterTransport.lower_17
#print axioms R1Z.PDict_FormatterTransport.lower_18
#print axioms R1Z.PDict_FormatterTransport.lower_19
#print axioms R1Z.PDict_FormatterTransport.lower_2
#print axioms R1Z.PDict_FormatterTransport.lower_20
#print axioms R1Z.PDict_FormatterTransport.lower_21
#print axioms R1Z.PDict_FormatterTransport.lower_22
#print axioms R1Z.PDict_FormatterTransport.lower_23
#print axioms R1Z.PDict_FormatterTransport.lower_24
#print axioms R1Z.PDict_FormatterTransport.lower_25
#print axioms R1Z.PDict_FormatterTransport.lower_3
#print axioms R1Z.PDict_FormatterTransport.lower_4
#print axioms R1Z.PDict_FormatterTransport.lower_5
#print axioms R1Z.PDict_FormatterTypeEquiv.compilationEquiv
#print axioms R1Z.PDict_FormatterTypeEquiv.lateEquiv
#print axioms R1Z.PDict_FormatterTypeEquiv.linkEquiv
#print axioms R1Z.PDict_FormatterTypeEquiv.pubEquiv
#print axioms R1Z.PDict_FormatterTypeEquiv.storeEquiv
#print axioms R1Z.PDict_FormatterTypeEquiv.timesEquiv
#print axioms R1Z.PDict_FormatterTypeEquiv.traceEquiv
#print axioms R1Z.PDict_FormatterTypeMaps.compilation_roundtrip
#print axioms R1Z.PDict_FormatterTypeMaps.late_roundtrip
#print axioms R1Z.PDict_FormatterTypeMaps.link_roundtrip
#print axioms R1Z.PDict_FormatterTypeMaps.public_roundtrip
#print axioms R1Z.PDict_FormatterTypeMaps.times_roundtrip
#print axioms R1Z.PDict_FormatterTypeMaps.trace_roundtrip
#print axioms R1Z.PDict_LimbLayout.limbs
#print axioms R1Z.PDict_LimbLayout.selected_layout
#print axioms R1Z.PDict_OwnedErrorCorrect.decode_encode
#print axioms R1Z.PDict_OwnedErrorCorrect.encode_decode
#print axioms R1Z.PDict_OwnedErrorCorrect.observe_error
#print axioms R1Z.PDict_OwnedErrorCorrect.observe_success
#print axioms R1Z.PDict_OwnedErrorCorrect.open_error
#print axioms R1Z.PDict_OwnedErrorCorrect.open_observation
#print axioms R1Z.PDict_OwnedErrorDictionary.reference_kind
#print axioms R1Z.PDict_OwnedErrorDictionary.reference_type3
#print axioms R1Z.PDict_OwnedErrorDictionary.reserve_reference
#print axioms R1Z.PDict_OwnedErrorObservation.failure
#print axioms R1Z.PDict_OwnedErrorObservation.reserve_error
#print axioms R1Z.PDict_OwnedErrorObservation.reserve_success
#print axioms R1Z.PDict_OwnedErrorObservation.success
#print axioms R1Z.PDict_OwnedErrorTransport.finish_transport
#print axioms R1Z.PDict_OwnedErrorTransport.reserve_transport
#print axioms R1Z.PDict_OwnedErrorTransport.source_factor
#print axioms R1Z.PDict_PureDictionary.op235_installed
#print axioms R1Z.PDict_PureDictionary.op236_installed
#print axioms R1Z.PDict_PureDictionary.op239_installed
#print axioms R1Z.PDict_PureDictionary.op240_installed
#print axioms R1Z.PDict_PureDictionary.op260_installed
#print axioms R1Z.PDict_PureDictionary.op37_installed
#print axioms R1Z.PDict_PureDictionary.op40_installed
#print axioms R1Z.PDict_PureDictionary.op41_installed
#print axioms R1Z.PDict_PureDictionary.op43_installed
#print axioms R1Z.PDict_PureDictionary.op44_installed
#print axioms R1Z.PDict_PureDictionary.op60_installed
#print axioms R1Z.PDict_PureEqCM31.exact
#print axioms R1Z.PDict_ReachCaller.op124_irrelevant
#print axioms R1Z.PDict_ReachCaller.op13_irrelevant
#print axioms R1Z.PDict_ReachCaller.op16_irrelevant
#print axioms R1Z.PDict_ReachCaller.op17_irrelevant
#print axioms R1Z.PDict_ReachCaller.op18_irrelevant
#print axioms R1Z.PDict_ReachCaller.op238_irrelevant
#print axioms R1Z.PDict_ReachCaller.op85_irrelevant
#print axioms R1Z.PDict_ReachErase.client_0
#print axioms R1Z.PDict_ReachErase.client_1
#print axioms R1Z.PDict_ReachErase.client_2
#print axioms R1Z.PDict_ReachErase.client_3
#print axioms R1Z.PDict_ReachErase.client_4
#print axioms R1Z.PDict_ReachErase.client_5
#print axioms R1Z.PDict_ReachErase.client_6
#print axioms R1Z.PDict_ReachErase.client_7
#print axioms R1Z.PDict_ReachErase.client_8
#print axioms R1Z.PDict_ReachErase.erase_352
#print axioms R1Z.PDict_ReachErase.erase_353
#print axioms R1Z.PDict_ReachErase.erase_354
#print axioms R1Z.PDict_ReachErase.erase_355
#print axioms R1Z.PDict_ReachErase.erase_356
#print axioms R1Z.PDict_ReachErase.erase_357
#print axioms R1Z.PDict_ReachErase.erase_358
#print axioms R1Z.PDict_ReachErase.erase_359
#print axioms R1Z.PDict_ReachErase.erase_360
#print axioms R1Z.PDict_ReachErase.erase_361
#print axioms R1Z.PDict_ReachErase.erase_362
#print axioms R1Z.PDict_ReachErase.erase_363
#print axioms R1Z.PDict_ReachErase.erase_364
#print axioms R1Z.PDict_ReachErase.erase_365
#print axioms R1Z.PDict_ReachErase.erase_366
#print axioms R1Z.PDict_ReachErase.erase_367
#print axioms R1Z.PDict_ReachErase.erase_368
#print axioms R1Z.PDict_ReachErase.erase_369
#print axioms R1Z.PDict_ReachErase.erase_370
#print axioms R1Z.PDict_ReachErase.erase_371
#print axioms R1Z.PDict_ReachErase.erase_372
#print axioms R1Z.PDict_ReachErase.erase_373
#print axioms R1Z.PDict_ReachErase.erase_374
#print axioms R1Z.PDict_ReachErase.erase_375
#print axioms R1Z.PDict_ReachErase.erase_376
#print axioms R1Z.PDict_ReachErase.erase_377
#print axioms R1Z.PDict_ReachErase.erase_378
#print axioms R1Z.PDict_ReachErase.erase_379
#print axioms R1Z.PDict_ReachErase.erase_380
#print axioms R1Z.PDict_ReachErase.erase_381
#print axioms R1Z.PDict_ReachErase.erase_382
#print axioms R1Z.PDict_ReachErase.erase_383
#print axioms R1Z.PDict_ReachErase.erase_384
#print axioms R1Z.PDict_ReachErase.erase_385
#print axioms R1Z.PDict_ReachErase.erase_386
#print axioms R1Z.PDict_ReachErase.erase_387
#print axioms R1Z.PDict_ReachErase.erase_388
#print axioms R1Z.PDict_ReachErase.erase_389
#print axioms R1Z.PDict_ReachErase.erase_390
#print axioms R1Z.PDict_ReachErase.erase_391
#print axioms R1Z.PDict_ReachErase.erase_392
#print axioms R1Z.PDict_ReachErase.erase_393
#print axioms R1Z.PDict_ReachErase.erase_394
#print axioms R1Z.PDict_ReachErase.erase_395
#print axioms R1Z.PDict_ReachErase.erase_396
#print axioms R1Z.PDict_ReachErase.erase_397
#print axioms R1Z.PDict_ReachErase.erase_398
#print axioms R1Z.PDict_ReachErase.erase_399
#print axioms R1Z.PDict_ReachErase.erase_400
#print axioms R1Z.PDict_ReachErase.erase_401
#print axioms R1Z.PDict_ReachErase.erase_402
#print axioms R1Z.PDict_ReachErase.erase_403
#print axioms R1Z.PDict_ReachErase.erase_404
#print axioms R1Z.PDict_ReachErase.erase_405
#print axioms R1Z.PDict_ReachErase.erase_406
#print axioms R1Z.PDict_ReachErase.erase_407
#print axioms R1Z.PDict_ReachErase.erase_408
#print axioms R1Z.PDict_ReachErase.erase_409
#print axioms R1Z.PDict_ReachErase.erase_410
#print axioms R1Z.PDict_ReachErase.erase_411
#print axioms R1Z.PDict_ReachErase.erase_412
#print axioms R1Z.PDict_ReachErase.erase_413
#print axioms R1Z.PDict_ReachErase.erase_414
#print axioms R1Z.PDict_ReachErase.erase_415
#print axioms R1Z.PDict_ReachErase.erase_416
#print axioms R1Z.PDict_ReachErase.erase_417
#print axioms R1Z.PDict_ReachErase.erase_418
#print axioms R1Z.PDict_ReachErase.erase_419
#print axioms R1Z.PDict_ReachErase.erase_420
#print axioms R1Z.PDict_ReachErase.erase_421
#print axioms R1Z.PDict_ReachErase.erase_422
#print axioms R1Z.PDict_ReachErase.erase_423
#print axioms R1Z.PDict_ReachErase.erase_424
#print axioms R1Z.PDict_ReachErase.erase_425
#print axioms R1Z.PDict_ReachErase.publication_frame
#print axioms R1Z.PDict_ReserveFailure.kind_divergence
#print axioms R1Z.PDict_ReserveFailure.kind_failure
#print axioms R1Z.PDict_ReserveFailure.source_divergence
#print axioms R1Z.PDict_ReserveFailure.source_failure
#print axioms R1Z.PDict_ResultTransport.bind_map
#print axioms R1Z.PDict_ResultTransport.map_bind
#print axioms R1Z.PDict_ResultTransport.map_comp
#print axioms R1Z.PDict_ResultTransport.map_div
#print axioms R1Z.PDict_ResultTransport.map_fail
#print axioms R1Z.PDict_ResultTransport.map_id
#print axioms R1Z.PDict_ResultTransport.map_ok

#print R1Z.ProverCommitDeployedFuel22.RustProverRefinement
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
