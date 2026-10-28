import NBA_Audit
import NBL_AddNative
import NBL_ArrayPort
import NBL_BlockTrace
import NBL_ByteWord
import NBL_CarryBounds
import NBL_ClaimDomain
import NBL_CodeMonad
import NBL_CodeRunLaws
import NBL_CohortCode
import NBL_ContinuationHash
import NBL_DecodeNative
import NBL_EffectControl
import NBL_HashReplay
import NBL_InitConstruct
import NBL_InitTrace
import NBL_MaterialHashReplay
import NBL_MaterialTrace
import NBL_OpeningHashReplay
import NBL_OpeningTrace
import NBL_PassBounds
import NBL_PassConstruct
import NBL_PrepareAutoRho
import NBL_PrepareControl
import NBL_PrepareHashReject
import NBL_PrepareHashTrace
import NBL_PrepareResults
import NBL_PrepareTrace
import NBL_QueryDictionary
import NBL_QueryEffectFactor
import NBL_QueryFinish
import NBL_QueryHashReplay
import NBL_QueryPort
import NBL_QueryQuietFinish
import NBL_QueryTrace
import NBL_QueryWalk
import NBL_QuietRun
import NBL_RhoConstruct
import NBL_RunStep
import NBL_SamplerDebug
import NBL_SamplerNative
import NBL_SamplerReplay
import NBL_ScalarConstruct
import NBL_ScalarHashReplay
import NBL_SecondCarry
import NBL_SlicePort
import NBL_ViewDomains
import NBL_ViewFields
import NBL_ViewNatural
import NBL_ViewOffsets
import NBL_ViewProduct
set_option autoImplicit false
set_option pp.fullNames true
#print axioms AspisR1.NBL_AddNative.source
#print axioms AspisR1.NBL_AddNative.canonical
#print axioms AspisR1.NBL_ArrayPort.source
#print axioms AspisR1.NBL_BlockTrace.block_result
#print axioms AspisR1.NBL_BlockTrace.block_log
#print axioms AspisR1.NBL_BlockTrace.scalar_result
#print axioms AspisR1.NBL_ByteWord.source
#print axioms AspisR1.NBL_CarryBounds.nonempty
#print axioms AspisR1.NBL_CarryBounds.source
#print axioms AspisR1.NBL_ClaimDomain.source
#print axioms AspisR1.NBL_CodeMonad.associative
#print axioms AspisR1.NBL_CodeMonad.bind_same
#print axioms AspisR1.NBL_CodeMonad.pure_bind
#print axioms AspisR1.NBL_CodeRunLaws.bind_run
#print axioms AspisR1.NBL_CodeRunLaws.lift_run
#print axioms AspisR1.NBL_CodeRunLaws.pure_run
#print axioms AspisR1.NBL_CodeRunLaws.digest_run
#print axioms AspisR1.NBL_CohortCode.dictionary
#print axioms AspisR1.NBL_CohortCode.erasure
#print axioms AspisR1.NBL_ContinuationHash.query_error
#print axioms AspisR1.NBL_ContinuationHash.tail
#print axioms AspisR1.NBL_ContinuationHash.after_opening
#print axioms AspisR1.NBL_DecodeNative.remainder
#print axioms AspisR1.NBL_DecodeNative.canonical_qm
#print axioms AspisR1.NBL_DecodeNative.source
#print axioms AspisR1.NBL_EffectControl.source
#print axioms AspisR1.NBL_HashReplay.absorb
#print axioms AspisR1.NBL_HashReplay.block
#print axioms AspisR1.NBL_HashReplay.seed
#print axioms AspisR1.NBL_InitConstruct.frame
#print axioms AspisR1.NBL_InitConstruct.trace
#print axioms AspisR1.NBL_InitConstruct.rho
#print axioms AspisR1.NBL_InitTrace.processed
#print axioms AspisR1.NBL_InitTrace.source
#print axioms AspisR1.NBL_InitTrace.rho
#print axioms AspisR1.NBL_MaterialHashReplay.source
#print axioms AspisR1.NBL_MaterialTrace.source
#print axioms AspisR1.NBL_OpeningHashReplay.source
#print axioms AspisR1.NBL_OpeningTrace.source
#print axioms AspisR1.NBL_OpeningTrace.log_length
#print axioms AspisR1.NBL_OpeningTrace.log_sound
#print axioms AspisR1.NBL_PassBounds.remainder
#print axioms AspisR1.NBL_PassBounds.canonical
#print axioms AspisR1.NBL_PassConstruct.pass
#print axioms AspisR1.NBL_PassConstruct.digits
#print axioms AspisR1.NBL_PassConstruct.pass_length
#print axioms AspisR1.NBL_PassConstruct.digits_length
#print axioms AspisR1.NBL_PrepareAutoRho.source
#print axioms AspisR1.NBL_PrepareControl.source
#print axioms AspisR1.NBL_PrepareHashReject.source
#print axioms AspisR1.NBL_PrepareHashTrace.source
#print axioms AspisR1.NBL_PrepareResults.query_error
#print axioms AspisR1.NBL_PrepareResults.claim_error
#print axioms AspisR1.NBL_PrepareResults.prepare_query_error
#print axioms AspisR1.NBL_PrepareResults.success
#print axioms AspisR1.NBL_PrepareResults.after_opening
#print axioms AspisR1.NBL_PrepareTrace.query_error
#print axioms AspisR1.NBL_PrepareTrace.success
#print axioms AspisR1.NBL_QueryDictionary.installed
#print axioms AspisR1.NBL_QueryEffectFactor.source
#print axioms AspisR1.NBL_QueryFinish.factor
#print axioms AspisR1.NBL_QueryFinish.error
#print axioms AspisR1.NBL_QueryFinish.success
#print axioms AspisR1.NBL_QueryHashReplay.source
#print axioms AspisR1.NBL_QueryHashReplay.length
#print axioms AspisR1.NBL_QueryPort.source
#print axioms AspisR1.NBL_QueryQuietFinish.source
#print axioms AspisR1.NBL_QueryTrace.source
#print axioms AspisR1.NBL_QueryWalk.source
#print axioms AspisR1.NBL_QueryWalk.construct
#print axioms AspisR1.NBL_QueryWalk.decoder
#print axioms AspisR1.NBL_QuietRun.bind
#print axioms AspisR1.NBL_RhoConstruct.source
#print axioms AspisR1.NBL_RunStep.lift_ok
#print axioms AspisR1.NBL_RunStep.digest_ok
#print axioms AspisR1.NBL_SamplerDebug.source
#print axioms AspisR1.NBL_SamplerNative.decode_gamma
#print axioms AspisR1.NBL_SamplerNative.ordinary
#print axioms AspisR1.NBL_SamplerNative.gamma_no_wrap
#print axioms AspisR1.NBL_SamplerNative.gamma_wrap
#print axioms AspisR1.NBL_SamplerReplay.low
#print axioms AspisR1.NBL_SamplerReplay.ordinary
#print axioms AspisR1.NBL_SamplerReplay.increment
#print axioms AspisR1.NBL_SamplerReplay.gamma_no_wrap
#print axioms AspisR1.NBL_SamplerReplay.gamma_wrap
#print axioms AspisR1.NBL_ScalarConstruct.source
#print axioms AspisR1.NBL_ScalarHashReplay.scalar
#print axioms AspisR1.NBL_ScalarHashReplay.rho
#print axioms AspisR1.NBL_SecondCarry.natural
#print axioms AspisR1.NBL_SlicePort.source
#print axioms AspisR1.NBL_SlicePort.length
#print axioms AspisR1.NBL_SlicePort.empty
#print axioms AspisR1.NBL_ViewDomains.source
#print axioms AspisR1.NBL_ViewFields.source
#print axioms AspisR1.NBL_ViewNatural.parser
#print axioms AspisR1.NBL_ViewNatural.source
#print axioms AspisR1.NBL_ViewOffsets.final
#print axioms AspisR1.NBL_ViewOffsets.openings
#print axioms AspisR1.NBL_ViewOffsets.source
#print axioms AspisR1.NBL_ViewProduct.source
#check @AspisR1.NBL_ViewNatural.source
#check @AspisR1.NBL_ViewDomains.source
#check @AspisR1.NBL_PrepareHashTrace.source
#check @AspisR1.NBL_PrepareHashReject.source
