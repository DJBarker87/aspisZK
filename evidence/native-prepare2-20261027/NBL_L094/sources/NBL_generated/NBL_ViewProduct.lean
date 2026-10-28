import NBL_ArrayPort
import NBL_ViewOffsets
import NBL_SlicePort
set_option autoImplicit false
namespace AspisR1.NBL_ViewProduct
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1
open NBL_SlicePort

def root (proof : Slice U8) (size : 10055≤proof.val.length) : Array U8 32#usize :=
  ⟨(segment proof 7751#usize 7783#usize).val,by
    have len := length proof 7751#usize 7783#usize (by decide) (by change 7783≤_;omega)
    exact len⟩

def rest (proof semantic y1 : Slice U8) (size : 10055≤proof.val.length)
    (inactive : aspis_core.field.wide_exact.WideExact) : verifier.View :=
  {variant:=.S2,semantic,y1,inactive,
   round0:=segment proof 7527#usize 7751#usize,folded_root:=some (root proof size),
   round1:=segment proof 7783#usize 8007#usize,
   final_message:=segment proof 8007#usize 10055#usize,query_bytes:=⟨[],by simp⟩}

def product (proof semantic y1 : Slice U8) (size : 10055≤proof.val.length)
    (inactive : Option aspis_core.field.wide_exact.WideExact) :
    core.result.Result verifier.View verifier.Error :=
  match inactive with
  | none => .Err .Parse
  | some value => .Ok (rest proof semantic y1 size value)

/-- Full selected nominal View/Parse Result from SAME native byte ranges and
local inactive parser result. No chosen successful View or field premises. -/
theorem source (proof semantic y1 : Slice U8) (size : 10055≤proof.val.length)
    (inactive : Option aspis_core.field.wide_exact.WideExact)
    (parsed : viewFromBytes (segment proof 7495#usize 7527#usize)=ok inactive) :
    verifier.candidate.wide_view proof semantic y1=ok (product proof semantic y1 size inactive) := by
  have s0 := NBL_SlicePort.source proof 7495#usize 7527#usize (by decide) (by change 7527≤_;omega)
  have s1 := NBL_SlicePort.source proof 7527#usize 7751#usize (by decide) (by change 7751≤_;omega)
  have s2 := NBL_SlicePort.source proof 7751#usize 7783#usize (by decide) (by change 7783≤_;omega)
  have s3 := NBL_SlicePort.source proof 7783#usize 8007#usize (by decide) (by change 8007≤_;omega)
  have s4 := NBL_SlicePort.source proof 8007#usize 10055#usize (by decide) (by change 10055≤_;omega)
  have rootSize : (segment proof 7751#usize 7783#usize).val.length=(32#usize).val :=
    (root proof size).property
  have rootCall : core.array.TryFromSharedArraySlice.try_from 32#usize
      (segment proof 7751#usize 7783#usize)=ok (.Ok (root proof size)) := by
    have call := NBL_ArrayPort.source (segment proof 7751#usize 7783#usize) 32#usize rootSize
    have same : (⟨(segment proof 7751#usize 7783#usize).val,rootSize⟩ : Array U8 32#usize)=root proof size :=
      Subtype.ext rfl
    exact call.trans (congrArg (fun x : Array U8 32#usize => Result.ok (core.result.Result.Ok x : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError)) same)
  unfold verifier.candidate.wide_view
  rw [AuS1_Offsets.inactive,bind_tc_ok,AuS1_Offsets.round0,bind_tc_ok,s0,bind_tc_ok,parsed,bind_tc_ok]
  cases inactive with
  | none =>
    simp only [product,viewOptionOkOr,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]
    rfl
  | some value =>
    simp only [viewOptionOkOr,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
      AuS1_Offsets.folded,s1,AuS1_Offsets.round1,s2,rootCall,core.result.Result.unwrap,
      NBL_ViewOffsets.final,s3,NBL_ViewOffsets.openings,s4,NBL_SlicePort.empty,product,rest]
#print axioms source
end AspisR1.NBL_ViewProduct
