import NHF_ViewConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHF_ViewCut
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev Out := core.result.Result verifier.View verifier.Error

def range (proof : Slice U8) (start finish : Usize) : Result (Slice U8) :=
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   proof {start:=start,«end»:=finish}

def finish (proof semantic y1 : Slice U8) (inactive : E) : Result Out := do
 let part0 ← range proof 7527#usize 7751#usize
 let root ← range proof 7751#usize 7783#usize
 let converted ← core.array.TryFromSharedArraySlice.try_from 32#usize root
 let rootArray ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted
 let part1 ← range proof 7783#usize 8007#usize
 let message ← range proof 8007#usize 10055#usize
 let emptyBytes ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   proof {«end»:=0#usize}
 ok (.Ok ⟨.S2, semantic, y1, inactive, part0, some rootArray, part1, message, emptyBytes⟩)

def dispatch (proof semantic y1 : Slice U8) (reply : Option E) : Result Out := do
 let r ← viewOptionOkOr reply verifier.Error.Parse
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue value => finish proof semantic y1 value
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     verifier.View (core.convert.FromSame verifier.Error) residual

/-- Exact emitted body with one local decoder cut; no return equality premise. -/
theorem source (proof semantic y1 : Slice U8) :
 verifier.candidate.wide_view proof semantic y1 =
 (do let bytes ← range proof 7495#usize 7527#usize
     let reply ← viewFromBytes bytes
     dispatch proof semantic y1 reply) := by
 simp only [verifier.candidate.wide_view,NHF_ViewConstants.inactive,
   NHF_ViewConstants.round0,NHF_ViewConstants.folded,NHF_ViewConstants.round1,
   NHF_ViewConstants.finalMessage,NHF_ViewConstants.openings,bind_tc_ok,
   dispatch,finish,range]

theorem reject (proof semantic y1 : Slice U8) :
 dispatch proof semantic y1 none = ok (.Err verifier.Error.Parse) := by rfl

theorem accepted (proof semantic y1 : Slice U8) (reply : E) :
 dispatch proof semantic y1 (some reply) = finish proof semantic y1 reply := by rfl
#print axioms source
#print axioms reject
#print axioms accepted
end AspisR1.NHF_ViewCut
end
