import JFw_Values
import PSem_RowStep
import PSem_Iterator
set_option autoImplicit false
namespace AspisR1.JFw_Row
open Aeneas Aeneas.Std Result WP ControlFlow
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation PSem_Iterator
attribute [local reducible] Aeneas.Std.WP.Post

 theorem spec (input out : Slice U8) (row nextRow tag : U8) (size src dst : Usize)
    (bound : row.val < 27) (next : nextRow.val = row.val+1)
    (shape : r1_wire.row_shape row = ok (some (tag,size)))
    (sizeBound : size.val ≤ 3712) (aligned : size.val % 32 = 0)
    (inputBound : src.val+5+(if 14 ≤ row.val then size.val/2 else size.val) ≤ input.length)
    (outBound : dst.val+5+size.val ≤ out.length)
    (smallInput : input.length ≤ 20000) (smallOut : out.length ≤ 20000) :
    compact.expand_semantic_loop.body nativeValues input (iter row) out src dst
      ⦃ result => ∃ updated nextSrc nextDst,
        result = .cont (iter nextRow,updated,nextSrc,nextDst) ∧
        updated.length = out.length ∧
        nextSrc.val = src.val+5+(if 14 ≤ row.val then size.val/2 else size.val) ∧
        nextDst.val = dst.val+5+size.val ⦄ := by
  unfold compact.expand_semantic_loop.body
  simp (config := {zeta := true}) only [next_row row nextRow bound next,
    bind_tc_ok,shape,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
  simp (config := {zeta := true}) only [shape,bind_tc_ok,core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch]
  step* <;> scalar_tac

#print axioms spec
end AspisR1.JFw_Row
