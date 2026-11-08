import NVR_NoWriteOwned
-- NVR_ provenance: copied from evidence/stage-wrap-20261111/NMV_NoWrite241.lean (research, sha256 51ee068eef86f5d3...).
-- Change: TGA_NMV_REV4.diff (sha256 dea825de) applied for RSL rev4; NMV_ -> NVR_ renames only otherwise.
set_option autoImplicit false
namespace NVR_NoWrite241
open RSL NMV_NoWrite NVR_NoWriteOwned

theorem error_free (V : TX2_241.V2Lib) (r : Except V.VErr Unit) :
 Free (TX2_241.mapVErr V r) := by
 cases r with
 | ok u => cases u; exact pure_free _
 | error e =>
   apply rs_seq_free _ _ (lift_free _ alloc_free)
   apply rs_seq_free
   · apply lift_free
     apply emit_free; intro c b h; cases h
   · exact pure_free _

theorem owned241_free (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (pl : PoolLaws L) (hw : ∀ p q r, Free (V.tx2auth p q r)) (a : TX2_241.Args) :
 Free (TX2_241.Ref L D V a) := by
 unfold TX2_241.Ref
 apply rs_seq_free _ _ (check_free _ _)
 apply rs_bind_free
 · exact call_free _ _ _ (validate_free L D pl _)
 · intro validated
   apply rs_bind_free _ _ (index_free _ _)
   intro acc0
   apply rs_bind_free _ _ (NVR_NoWritePool.data_free _)
   intro proofData
   apply rs_bind_free _ _ (index_free _ _)
   intro acc6
   apply rs_bind_free _ _ (NVR_NoWritePool.data_free _)
   intro checkpointData
   apply rs_seq_free _ _ (check_free _ _)
   apply rs_seq_free _ _ (check_free _ _)
   apply rs_bind_free _ _ (lift_free _ (pl.encode validated.statement))
   intro enc
   apply rs_bind_free _ _ (ofOption_free _ _)
   intro publicBytes
   apply rs_seq_free _ _ (check_free _ _)
   apply rs_bind_free
   · apply lift_free
     exact call_free _ _ _ (hw _ _ _)
   · intro r
     exact rs_seq_free _ _ (error_free V r) (pl.emit validated.statement)

#print axioms error_free
#print axioms owned241_free
end NVR_NoWrite241
