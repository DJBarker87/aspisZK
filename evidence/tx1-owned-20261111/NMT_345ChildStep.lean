import NMT_345TailChild
import NMT_345Raw_12
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result

def splitBounds {W : Type} (s : HasSplit W) : Bounds W :=
 s.toHasSplitByte.toHasProofSlice.toHasPublic.toTagExpected.toTagByte.toTagOffset.toPrefixReply.toHasPrefix.toBounds
/-- Open328 is called with the exact semantic Public, original public bytes,
selected proof slice and cast split. No endpoint or successful reply premise. -/
theorem stepChild {W : Type} (c : Calls) (s : HasSplit W) :
 tailChild c s = tryStep (c.c11 s.semanticPublic s.publicData s.proofSlice s.split)
   (fun checkpoint => raw12 c ⟨splitBounds s,checkpoint⟩) := by
 unfold tailChild tryStep
 cases h : c.c11 s.semanticPublic s.publicData s.proofSlice s.split with
 | fail e => simp only [h,bind_tc_fail]
 | div => simp only [h,bind_tc_div]
 | ok r =>
  cases r with
  | Err e =>
   simp only [h,bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    Aeneas.Std.core.convert.FromSame,Aeneas.Std.core.convert.FromSame.from]
  | Ok value =>
   simp only [h,bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
   rfl

theorem child_original_frame {W : Type} (s : HasSplit W) :
 ((splitBounds s).program,(splitBounds s).accounts,(splitBounds s).data,
  (splitBounds s).world,(splitBounds s).events) = (s.program,s.accounts,s.data,s.world,s.events) := rfl
#print axioms stepChild
#print axioms child_original_frame
end NMT_345
