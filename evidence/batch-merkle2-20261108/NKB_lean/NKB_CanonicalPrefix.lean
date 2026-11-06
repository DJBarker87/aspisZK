import NKB_CanonicalRowsLoop
import NKB_CanonicalConstants
set_option autoImplicit false
namespace NKB_CanonicalPrefix
open Aeneas Aeneas.Std Result ControlFlow AspisR1 NKB_CanonicalRange NKB_CanonicalPair NKB_CanonicalOpening NKB_CanonicalConstants

def values (proof : Slice U8) := MultiproofConeSlices.sub proof 7031#usize 7495#usize
def inactive (proof : Slice U8) := MultiproofConeSlices.sub proof 7495#usize 7527#usize
def round0 (proof : Slice U8) := MultiproofConeSlices.sub proof 7527#usize 7751#usize
def round1 (proof : Slice U8) := MultiproofConeSlices.sub proof 7783#usize 10055#usize

def guard (cv ec : Slice U8→Bool) (proof : Slice U8) : Bool :=
 cv (values proof) && ec (inactive proof) && ec (round0 proof) && ec (round1 proof)

def codec (b : Bool) : core.result.Result Unit NJS_Extract.compact.CodecError :=
 if b then .Ok () else .Err .NonCanonical

/-- Entire emitted canonical_scan for total child interpretations. This
source theorem preserves all first-Parse branches and proves the pending-None
panic arm unreachable. It remains parameterized and is NOT a CLOSED row root:
concrete codec/echeck substitution, native full cuts and adopted-model equality
are separate outstanding obligations. -/
theorem source (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (ec cv : Slice U8→Bool) (proof : Slice U8) (length : proof.val.length=57607) :
 NJS_Extract.verifier.candidate.canonical_scan
  (fun b=>ok (f b)) (fun b=>ok (g b)) (fun b _=>ok (reply (ec b)))
  (fun b=>ok (codec (cv b))) proof=
 ok (reply (guard cv ec proof && allFrom (NKB_CanonicalRows.pass f g ec proof) 0 22)) := by
 have y:=MultiproofConeSlices.range_total proof 7031#usize 7495#usize (by decide) (by change 7495≤proof.val.length;omega)
 have a:=MultiproofConeSlices.range_total proof 7495#usize 7527#usize (by decide) (by change 7527≤proof.val.length;omega)
 have b:=MultiproofConeSlices.range_total proof 7527#usize 7751#usize (by decide) (by change 7751≤proof.val.length;omega)
 have c:=MultiproofConeSlices.range_total proof 7783#usize 10055#usize (by decide) (by change 10055≤proof.val.length;omega)
 have rows:=NKB_CanonicalRowsLoop.source f g ec proof length 22 {start:=0#usize,«end»:=22#usize} rfl (by rfl)
 have add : Usize.wrapping_add 7495#usize 32#usize=7527#usize:=by
   apply UScalar.eq_of_val_eq
   rw [Usize.wrapping_add_val_eq]
   change 7527%UScalar.size .Usize=7527
   apply Nat.mod_eq_of_lt
   rw [UScalar.size_def]
   scalar_tac
 simp only [reply] at rows
 unfold NJS_Extract.verifier.candidate.canonical_scan
 simp only [off_y1,off_inactive,off_round0,off_folded_root,off_round1,off_openings,lift,add,bind_tc_ok]
 cases hy:cv (values proof) <;> cases ha:ec (inactive proof) <;>
 cases hb:ec (round0 proof) <;> cases hc:ec (round1 proof) <;>
 cases hr:allFrom (NKB_CanonicalRows.pass f g ec proof) 0 22 <;>
 simp [values,inactive,round0,round1] at hy ha hb hc <;>
 simp [y,a,b,c,hy,ha,hb,hc,rows,show (0#usize).val=0 from rfl,hr,
   guard,values,inactive,round0,round1,codec,reply,core.result.Result.Insts.CoreOpsTry.branch,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   NJS_Extract.verifier.Error.Insts.CoreConvertFromCodecError,NJS_Extract.verifier.Error.Insts.CoreConvertFromCodecError.from]

#print axioms source
end NKB_CanonicalPrefix
