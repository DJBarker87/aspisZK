import NLK_LaneHeader
import NLK_LaneDigest
import NLK_LaneTable
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NLK_LaneLoop
open Aeneas Aeneas.Std Result
open NKP_LaneCuts
abbrev Sized := NLK_LaneInput.Sized

def raw (p : Sized) (level : Fin 20) : core.result.Result Node Unit :=
 NLK_LaneDigest.decode (NLK_LaneInput.frontier p level)

def occupied (next : U64) (level : Fin 20) : Bool := next.val.testBit level.val

def zero : Frontier := fun _ _ => 0#u32
def levels : List (Fin 20) := List.finRange 20

def step (p : Sized) (next : U64) (before : Frontier) (level : Fin 20) :=
 NKF_LaneTrace.iteration (NLK_LaneTable.empty level) (occupied next level) before level (raw p level)

/-- The per-iteration window schema at SAME bytes. The raw decoder is already
instantiated internally; this is the canonical value step used by the fold. -/
theorem step_cut (p : Sized) (next : U64) (before : Frontier) (level : Fin 20) :
 IterationCut (NLK_LaneTable.empty level) (occupied next level) before
  (step p next before level).2 level (raw p level) (step p next before level).1 := by
 unfold step
 cases h : raw p level with
 | Err e =>
   exact { result:=rfl,selected:=fun _ => rfl,frame:=fun _ _ _ => rfl }
 | Ok node =>
   rw [NKF_LaneFactor.success_step]
   exact {
    result:=rfl
    selected:=fun word => congrFun (NJD_LaneStep.written before level node) word
    frame:=fun other different word =>
      congrFun (NJD_LaneStep.frame before level other node different) word }

theorem fold (p : Sized) (next : U64) :
 NKP_LaneInduction.fold (step p next) levels zero =
 NKF_LaneTrace.run NLK_LaneTable.empty (occupied next) (raw p) levels zero :=
 NKP_LaneInduction.compose NLK_LaneTable.empty (occupied next) (raw p)
  (step p next) (step_cut p next) levels zero

/-- Native usize/u64 shifts are in range at every source occurrence. -/
theorem shift_domain (level : Fin 20) : level.val<64 := by omega

theorem count : levels.length=20 := by simp only [levels,List.length_finRange]

#print step_cut
#print axioms step_cut
#print axioms fold
#print axioms shift_domain
#print axioms count
end NLK_LaneLoop
