import RPz7_GExp_FirstCode
import NLJ_RowSpec081
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Tx1
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev Scratch := Array aspis_core.field.wide_exact.WideExact 29#usize
abbrev Root := Array U8 32#usize
abbrev Out := core.result.Result (alloc.vec.Vec U8) verifier.Error
structure Input where
 base : Ops
 boundaries : AspisR1PublicPreparation.FinishModel.Boundaries
 std : ClaimsUnrolledFinish.StdCalls
 hashv : SdkC_Source.Parts → Result SdkC_Source.Digest
 digest : aspis_core.digest.Digest32 Unit
 publicValue : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
 publicBytes proof : Slice U8
 k : Usize

def ops (i : Input) : Ops := GExp_FirstCode.installed i.base i.boundaries i.std
inductive Local where
 | guard | parse | scan | markParsed | zero
 | prepare (scratch : Scratch)
 | accumulator (scratch : Scratch) (prepared : verifier.Prepared)
 | markPrepare (scratch : Scratch) (prepared : verifier.Prepared) (accumulator : verifier.Accumulator)
 | foldedSlice (scratch : Scratch) (prepared : verifier.Prepared) (accumulator : verifier.Accumulator)
 | foldedCopy (scratch : Scratch) (prepared : verifier.Prepared) (accumulator : verifier.Accumulator) (slice : Slice U8)
 | foldedUnwrap (scratch : Scratch) (prepared : verifier.Prepared) (accumulator : verifier.Accumulator) (reply : core.result.Result Root core.array.TryFromSliceError)
 | batch0 (scratch : Scratch) (prepared : verifier.Prepared) (accumulator : verifier.Accumulator) (folded : Root)
 | markMerkle (scratch : Scratch) (prepared : verifier.Prepared) (accumulator : verifier.Accumulator)
 | geometry (scratch : Scratch) (prepared : verifier.Prepared) (accumulator : verifier.Accumulator)
 | pending (scratch : Scratch) (prepared : verifier.Prepared) (accumulator : verifier.Accumulator) (geometry : verifier.QueryGeometry)
 | query (scratch : Scratch) (prepared : verifier.Prepared) (accumulator : verifier.Accumulator) (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 | finishPending (prepared : verifier.Prepared) (accumulator : verifier.Accumulator) (pending : verifier.BatchedWeights)
 | checkpoint (prepared : verifier.Prepared) (accumulator : verifier.Accumulator)
 | markCheckpoint (bytes : alloc.vec.Vec U8)
 | returned (bytes : alloc.vec.Vec U8)
inductive Event where
 | guard | parse | scan | markParsed | zero | prepare | accumulator | markPrepare
 | foldedSlice | foldedCopy | foldedUnwrap | batch0 | markMerkle | geometry
 | pending | query | finishPending | checkpoint | markCheckpoint | returned
 deriving DecidableEq, Repr
structure State where
 input : Input
 locals : Local
abbrev Post := Sum Out State

def advance (s : State) (l : Local) : State := {s with locals:=l}
def event (s : State) : Event :=
 match s.locals with
 | .guard => .guard | .parse => .parse | .scan => .scan | .markParsed => .markParsed | .zero => .zero
 | .prepare _ => .prepare | .accumulator _ _ => .accumulator | .markPrepare _ _ _ => .markPrepare
 | .foldedSlice _ _ _ => .foldedSlice | .foldedCopy _ _ _ _ => .foldedCopy | .foldedUnwrap _ _ _ _ => .foldedUnwrap
 | .batch0 _ _ _ _ => .batch0 | .markMerkle _ _ _ => .markMerkle | .geometry _ _ _ => .geometry
 | .pending _ _ _ _ => .pending | .query _ _ _ _ _ => .query | .finishPending _ _ _ => .finishPending
 | .checkpoint _ _ => .checkpoint | .markCheckpoint _ => .markCheckpoint | .returned _ => .returned
end AspisR1.NLJ_Tx1
end
