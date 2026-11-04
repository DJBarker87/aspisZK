import Lean
import NFN_PhaseTransport
import NEG_PrefixStep
import NFS_NCB_PrefixCutTrace

set_option autoImplicit false
noncomputable section
namespace NFS_NEI_PrefixStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1

/-- The same prestate read, appended value, product and index; arbitrary U32 flat. -/
theorem active (flat : Slice U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) (size : flat.val.length ≤ 110)
    (length : prefixes.val.length = index.val) (running : index.val < flat.val.length) :
    ∃ ps z next, NEG_PrefixFull.batch_prefix_products_loop.body flat prefixes product index =
      ok (cont (ps,z,next)) ∧ ps.val = prefixes.val ++ [product] ∧
      z.val = (product.val * (flat.val[index.val]'running).val) % 2147483647 ∧
      z.val < 2147483647 ∧ next.val = index.val + 1 := by
  obtain ⟨value,read,hvalue⟩ := WP.spec_imp_exists (Slice.index_usize_spec flat index running)
  change value = flat.val[index.val] at hvalue
  have capacity : prefixes.val.length < Usize.max := by
    have roomy : 110 < Usize.max := by scalar_tac
    omega
  obtain ⟨ps,push,pval⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec prefixes product capacity)
  obtain ⟨z,mul,natural,canonical⟩ := NEG_PrefixStep.multiply product value
  have exactProduct : z.val = (product.val * (flat.val[index.val]'running).val) % 2147483647 := by
    simpa only [hvalue] using natural
  obtain ⟨next,nextValue,body⟩ := NFS_NCB_PrefixNativeStep.source NEG_PrefixAssociation.ops rfl
    flat prefixes ps product z index size running (by omega) pval exactProduct
  exact ⟨ps,z,next,(NEG_PrefixAssociation.step flat prefixes product index).trans body,
    pval,exactProduct,canonical,nextValue⟩

theorem stopped (flat : Slice U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) (done : flat.val.length ≤ index.val) :
    NEG_PrefixFull.batch_prefix_products_loop.body flat prefixes product index =
      ok (ControlFlow.done (prefixes,product)) := by
  exact (NEG_PrefixAssociation.step flat prefixes product index).trans
    (NFS_NCB_PrefixNativeStep.stopped NEG_PrefixAssociation.ops flat prefixes product index done)

/-- Reuse the proved finite induction; no native whole-buffer run is assumed. -/
theorem total (flat : Slice U32) (size : flat.val.length ≤ 110) :
    ∃ ps product, NEG_PrefixFull.batch_prefix_products flat = ok (ps,product) ∧
      (ps.val,product) = S7Kani2PrefixLoop.model flat.val [] 1#u32 := by
  obtain ⟨ps,product,run,meaning⟩ := Port4C_PrefixMeaning.total NEG_PrefixAssociation.ops rfl rfl flat size
  exact ⟨ps,product,(NEG_PrefixAssociation.source flat).trans run,meaning⟩

#print axioms active
#print axioms stopped
#print axioms total
end NFS_NEI_PrefixStep
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
