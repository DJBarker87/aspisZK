import R1Z.PV_RunJoin_WeightMaterialResult47
import R1Z.PV_RunJoin_WeightInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WeightMaterialInstalled47
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_WeightInstalled46 (types Heap Box selected)
abbrev ME := AspisR1ProducerRelease47.field.wide_exact.WideExact
abbrev Native := PV_B2_F_MaterializeNative.Native

def native (x : ME) : Native :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

def nativeRust : PV_RunJoin_WeightMaterialResult47.MResult →
    core.result.Result (alloc.vec.Vec Native) ProverRwFull.verifier.Error
  | .Ok out => .Ok ⟨out.val.map native,by rw [List.length_map,out.property];scalar_tac⟩
  | .Err e => .Err (PV_B2_F_MaterializeNative.toError e)

theorem scalar (x : PV_RunJoin_WeightWide46.E) :
    native (PV_RunJoin_WeightWide46.toWide x)=PV_B2_F_MaterializeNative.toNative x := rfl
#print axioms scalar

theorem compose (r : PV_B2_F_AllocationTransport.RustResult) :
    nativeRust (PV_RunJoin_WeightMaterialResult47.mapRust r)=PV_B2_F_MaterializeNative.mapRust r := by
  cases r with
  | Err e => rfl
  | Ok out =>
    apply congrArg core.result.Result.Ok
    apply Subtype.ext
    change (out.val.map PV_RunJoin_WeightWide46.toWide).map native=
      out.val.map PV_B2_F_MaterializeNative.toNative
    simp only [List.map_map,Function.comp_def,scalar]
#print axioms compose

theorem complete (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : PV_RunJoin_WeightCarrier46.W)
    (hs : w.variant=.S2) (x : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base) (selected base heap box ops) w x=
      mapResult nativeRust (PV_RunJoin_WeightMaterialResult47.run (heap w x) w
        (PV_B2_F_MaterializeNative.fromNative x)) := by
  rw [PV_RunJoin_WeightInstalled46.materialize]
  unfold PV_B2_F_ResourceFamilies.heapOriginal
  rw [←PV_RunJoin_WeightMaterialResult47.original (heap w x) w hs]
  rw [PV_RunJoin_WeightArray46.result_comp]
  simp only [compose]
#print axioms complete
end R1Z.PV_RunJoin_WeightMaterialInstalled47
