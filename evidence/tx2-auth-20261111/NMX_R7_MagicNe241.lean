import NMX_R7_Prefix241
set_option autoImplicit false
noncomputable section
namespace NMX_R7_MagicNe241
open Aeneas Aeneas.Std Result AdapterRw
attribute [local instance] Classical.propDecidable

theorem native (env : RSL.Env) (a : Option (Slice U8)) (b : Slice U8) :
 core.cmp.PartialEq.ne.trait_default
  (core.option.Option.Insts.CoreCmpPartialEqOption (NMX_R7_Std241.ops env)
   (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8))) a (some b) =
 ok (match a with | none => true | some x => decide (x.val ≠ b.val)) := by
 cases a with
 | none => rfl
 | some x =>
   simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    core.option.Option.Insts.CoreCmpPartialEqOption,NMX_R7_Std241.ops,NMX_R7_Std241.optionEq,
    core.cmp.PartialEqShared,core.cmp.impls.PartialEqShared.eq,Slice.Insts.CoreCmpPartialEqSlice]
   rw [AspisS6StdByteSlice.eq_exact,bind_tc_ok]
   by_cases same : x.val = b.val <;> simp [same]

theorem byteList_injective : Function.Injective (List.map NMS_R2N_RSLScalars.u8) := by
 intro a b same
 have inverse := congrArg (List.map NMS_R2N_RSLScalars.raw8) same
 simp only [List.map_map,Function.comp_def,NMS_R2N_RSLScalars.u8_left] at inverse
 change List.map id a = List.map id b at inverse
 simpa only [List.map_id] using inverse

#print axioms native
#print axioms byteList_injective
end NMX_R7_MagicNe241
end
