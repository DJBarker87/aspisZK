import NNG_ChildSource345
import NMT_345SourceFold
import NMT_345ReadonlyProof
import NMT_345ZeroSource
import NMT_345Decoder
import NMT_345Validator
import NMT_345Encoder
import NMT_345Common
import NMT_345Semantic
import NMT_345EqByte
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Calls345
open Aeneas Aeneas.Std Result NMT_345 NMT_stage1_owned

def eqArray {T U : Type} {N : Usize} (inst : core.cmp.PartialEq T U) (xs : Slice T) (ys : Array U N) : Result Bool :=
 NMT_345Std.listEq inst.eq xs.val ys.val
def neArray {T U : Type} {N : Usize} (inst : core.cmp.PartialEq T U) (xs : Slice T) (ys : Array U N) : Result Bool := do
 let equal ← eqArray inst xs ys
 ok (!equal)

/-- Source dictionary only, not a VLib instance. Every value is a named
concrete CLOSED model or an emitted/std supplement; no child parameter. -/
def calls (env : RSL.Env) : Calls where
 c0:=neArray
 c1:=eqArray
 c2:=fun inst r o=>NMT_first.NMT_std_map_err inst r o
 c3:=fun v=>ok (match v with | .S1=>1#u8 | .S2=>2#u8 | .D=>3#u8)
 c4:=ok 57607#usize
 c5:=semanticCall
 c6:=commonCall
 c7:=validateCall
 c8:=ok 688#usize
 c9:=encodeCall
 c10:=fun e=>ok e
 c11:=NNG_ChildSource345.call env
 c12:=decodeCall
 c13:=readonlyCall
 c14:=fun a program writable=>mapOuter (mapCore id fromPE)
  (AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
   (NGL_CheckpointModel.install baseOps) (toAccount a) program writable)
 c15:=fun accounts=>mapOuter (mapCore id fromPE)
  (AdapterRw.r1_pool_adapter.owned.require_distinct_accounts (NGL_ReadonlyModel.install baseOps) (oldArray accounts))
 c16:=zeroCall
end AspisR1.NNG_Calls345
