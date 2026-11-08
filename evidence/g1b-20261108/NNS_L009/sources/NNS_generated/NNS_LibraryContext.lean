import NNS_Fold241
set_option autoImplicit false
namespace NNS_LibraryContext
open RSL RSL.TX2_241 NMS_R2Replay241
variable (L : PoolLib) (V : V2Lib) (R0 : Bytes → Bytes → Prop)
 (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))

theorem map_error (r : Except V.VErr Unit) :
 mapVErr (TAS.lib V R0 w) r = mapVErr V r := rfl

theorem after_public (verify : VerifyArgs → Spec (Except V.VErr Unit))
 (v : TX2_242.Validated L) (pr ck pub : Bytes) :
 afterPublic L (TAS.lib V R0 w) verify v pr ck pub = afterPublic L V verify v pr ck pub := by
 unfold afterPublic
 simp only [map_error]

theorem after_reads (verify : VerifyArgs → Spec (Except V.VErr Unit))
 (v : TX2_242.Validated L) (pr ck : Bytes) :
 afterReads L (TAS.lib V R0 w) verify v pr ck = afterReads L V verify v pr ck := by
 unfold afterReads
 simp only [after_public]

theorem after_validate (verify : VerifyArgs → Spec (Except V.VErr Unit))
 (a : Args) (v : TX2_242.Validated L) :
 afterValidate L (TAS.lib V R0 w) verify a v = afterValidate L V verify a v := by
 unfold afterValidate
 simp only [after_reads]

theorem replay (validate : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L)))
 (verify : VerifyNative V) (a : Args) :
 NMS_R2Replay241.replay L (TAS.lib V R0 w) validate verify a =
 NMS_R2Replay241.replay L V validate verify a := by
 unfold NMS_R2Replay241.replay
 simp only [after_validate]

#print axioms map_error
#print axioms after_public
#print axioms after_reads
#print axioms after_validate
#print axioms replay
end NNS_LibraryContext
