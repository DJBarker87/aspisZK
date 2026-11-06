import RPz7_SdkD_PrepareSource
import NKQ_PrepareBuffer
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev Scratch := Array aspis_core.field.wide_exact.WideExact 29#usize
abbrev Out := core.result.Result verifier.Prepared verifier.Error × Scratch
abbrev VecBack := Slice U8 → alloc.vec.Vec U8
abbrev SplitBack := Slice U8 × Slice U8 → Slice U8
structure Configuration where
 base : Ops
 boundaries : AspisR1PublicPreparation.FinishModel.Boundaries
 std : ClaimsUnrolledFinish.StdCalls
structure Input (H : Type) where
 digest : aspis_core.digest.Digest32 H
 publicValue : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
 proof : Slice U8
 hash : H
 scratch : Scratch
/-- Source installation is fixed by this input. This is not an admissible
arbitrary Ops premise in a native row root. -/
def ops (c : Configuration) : Ops := RowShape_InstalledSlots.verifierOps c.base c.boundaries c.std
inductive Local (H : Type) where
 | allocate
 | split (length : Usize) (logical : alloc.vec.Vec U8)
 | semanticRange (length : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 | expandSemantic (length offY1 : Usize) (semantic y1 compressed : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 | valueRange (length offY1 : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 | expandValues (length : Usize) (semantic y1 compressed : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 | rebuild (length : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 | view (logical : alloc.vec.Vec U8) (semantic y1 : Slice U8)
 | semantic (logical : alloc.vec.Vec U8) (view : verifier.View)
 | mapSemantic (logical : alloc.vec.Vec U8) (view : verifier.View) (reply : core.result.Result (r1_semantic.Verified H) r1_wire.Error)
 | mark (logical : alloc.vec.Vec U8) (view : verifier.View) (verified : r1_semantic.Verified H)
 | constructor (logical : alloc.vec.Vec U8) (view : verifier.View) (verified : r1_semantic.Verified H)
inductive Event where
 | allocate | split | semanticRange | expandSemantic | valueRange | expandValues
 | rebuild | view | semantic | mapSemantic | mark | constructor
 deriving DecidableEq, Repr
structure State (H : Type) where
 input : Input H
 locals : Local H
abbrev Post (H : Type) := Sum Out (State H)
def advance {H : Type} (s : State H) (l : Local H) : State H := {s with locals:=l}
def event {H : Type} (s : State H) : Event :=
 match s.locals with
 | .allocate => .allocate | .split _ _ => .split | .semanticRange _ _ _ _ _ => .semanticRange
 | .expandSemantic _ _ _ _ _ _ _ => .expandSemantic | .valueRange _ _ _ _ _ _ => .valueRange
 | .expandValues _ _ _ _ _ _ => .expandValues | .rebuild _ _ _ _ _ => .rebuild
 | .view _ _ _ => .view | .semantic _ _ => .semantic | .mapSemantic _ _ _ => .mapSemantic
 | .mark _ _ _ => .mark | .constructor _ _ _ => .constructor
end AspisR1.NLJ_Prepare
end
