import NMX_R8_MagicGet
set_option autoImplicit false
noncomputable section
namespace NMX_R8_MagicCheck
open Aeneas Aeneas.Std Result AdapterRw
attribute [local instance] Classical.propDecidable
abbrev magic := aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC

theorem mapped_eq (data : Slice U8) :
 (NMX_R8_MagicGet.first data).val = magic.val ↔
 (NMS_R2N_RSLScalars.bytes data).take 4 = RSL.REQUEST_MAGIC := by
 rw [←NMX_R7_Prefix241.magic]
 change data.val.take 4 = magic.val ↔
  (data.val.map NMS_R2N_RSLScalars.u8).take 4 = magic.val.map NMS_R2N_RSLScalars.u8
 rw [←List.map_take]
 exact ⟨congrArg (List.map NMS_R2N_RSLScalars.u8),fun same => NMX_R7_MagicNe241.byteList_injective same⟩

theorem full (env : RSL.Env) (data : Slice U8) :
 NMX_R7_Prefix241.magicCheck env data = ok
  (decide ((NMS_R2N_RSLScalars.bytes data).length < 4) ||
   ((NMS_R2N_RSLScalars.bytes data).take 4 != RSL.REQUEST_MAGIC)) := by
 unfold NMX_R7_Prefix241.magicCheck
 rw [NMX_R8_MagicGet.get]
 by_cases bound : 4 ≤ data.val.length
 · rw [if_pos bound,bind_tc_ok]
   change core.cmp.PartialEq.ne.trait_default
    (core.option.Option.Insts.CoreCmpPartialEqOption (NMX_R7_Std241.ops env)
      (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)))
    (some (NMX_R8_MagicGet.first data)) (some magic.to_slice) = _
   rw [NMX_R7_MagicNe241.native]
   have notshort : ¬(NMS_R2N_RSLScalars.bytes data).length < 4 := by
    rw [NMS_R2N_RSLScalars.bytes_length]; omega
   by_cases same : (NMX_R8_MagicGet.first data).val = magic.val
   · have hs := (mapped_eq data).mp same
     simp [same,hs,notshort]
   · have hs : (NMS_R2N_RSLScalars.bytes data).take 4 ≠ RSL.REQUEST_MAGIC :=
      fun eq => same ((mapped_eq data).mpr eq)
     simp [same,hs,notshort]
 · rw [if_neg bound,bind_tc_ok]
   change core.cmp.PartialEq.ne.trait_default
    (core.option.Option.Insts.CoreCmpPartialEqOption (NMX_R7_Std241.ops env)
      (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)))
    none (some magic.to_slice) = _
   rw [NMX_R7_MagicNe241.native]
   have short : (NMS_R2N_RSLScalars.bytes data).length < 4 := by
    rw [NMS_R2N_RSLScalars.bytes_length]; omega
   simp [short]
#print axioms mapped_eq
#print axioms full
end NMX_R8_MagicCheck
end
