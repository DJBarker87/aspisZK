import Lean
import NFY_Part032
import NGE_NEL_DigestGeometry
import NFY_Part029

set_option autoImplicit false
noncomputable section
namespace NGE_NEL_DigestLoopFrame
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder AspisR1.S2K

/-- Native byte-update observations are associated with the SAME emitted
protocol step, not an independently selected digest or output allocation. -/
theorem step_and_bytes (digest : Array U32 8#usize) (index : Usize)
    (range : index.val < 8) (out : Array U8 32#usize) :
    ∃ next, ∃ after : Array U8 32#usize,
      atomic_statement.encode_digest_canonical_loop.body (DigestTotal.cursor digest index) out =
        ok (.cont (next,after)) ∧
      ∀ k : Nat, after.val[k]? =
        KMX_CopyMeaning.loop
          (fun j => (core.num.U32.to_le_bytes
            (digest.val[index.val]'(by have := digest.property; change digest.val.length=8 at this; omega))).val[j-4*index.val]?)
          (fun j => out.val[j]?) (4*index.val) 4 k := by
  refine ⟨_,_,NFY_NBP_DigestEncode.step digest index range out,?_⟩
  intro k
  exact (NFY_NEL_CopyArrayLaw.loop_binding out
    (core.num.U32.to_le_bytes
      (digest.val[index.val]'(by have := digest.property; change digest.val.length=8 at this; omega)))
    (4*index.val) k (by change 4*index.val+4 ≤ 32; omega)).symm

#print axioms step_and_bytes
end NGE_NEL_DigestLoopFrame

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
