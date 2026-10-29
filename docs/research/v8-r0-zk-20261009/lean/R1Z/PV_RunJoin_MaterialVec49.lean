import R1Z.PV_RunJoin_WeightMaterialInstalled47
import R1Z.PV_RunJoin_ResultImage49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaterialVec49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightMap46 (mapResult)
abbrev S := AspisR1ProducerRelease47.field.wide_exact.WideExact
abbrev W := aspis_core.field.wide_exact.WideExact

def vec (a : Array S 1024#usize) : alloc.vec.Vec W :=
  ⟨a.val.map ProverRwDictionaryTower.fromW,by rw [List.length_map,a.property];scalar_tac⟩

theorem scalar (x : S) : PV_RunJoin_WeightMaterialInstalled47.native x=ProverRwDictionaryTower.fromW x := rfl

theorem input (x : S) : PV_RunJoin_WeightWide46.toWide
    (PV_B2_F_MaterializeNative.fromNative (ProverRwDictionaryTower.fromW x))=x := by
  cases x;rfl

theorem payload (a : Array S 1024#usize) :
    PV_RunJoin_WeightMaterialInstalled47.nativeRust (.Ok a)=.Ok (vec a) := by
  apply congrArg core.result.Result.Ok
  apply Subtype.ext
  change a.val.map PV_RunJoin_WeightMaterialInstalled47.native=a.val.map ProverRwDictionaryTower.fromW
  exact congrArg (fun f => a.val.map f) (funext scalar)

theorem wrap (r : Result (Array S 1024#usize)) :
    mapResult PV_RunJoin_WeightMaterialInstalled47.nativeRust (do let out ← r;ok (.Ok out))=
      (do let out ← r;ok (.Ok (vec out))) := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok a => exact congrArg Result.ok (payload a)
#print axioms vec
#print axioms scalar
#print axioms input
#print axioms payload
#print axioms wrap
end R1Z.PV_RunJoin_MaterialVec49
