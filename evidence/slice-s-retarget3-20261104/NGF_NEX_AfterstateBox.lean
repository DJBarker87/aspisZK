import Lean
import NGF_NED_AfterBoxComposition
import NFY_Part058

set_option autoImplicit false
noncomputable section
namespace NGF_NEX_AfterstateBox
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Value := pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

def run (bytes : Slice U8) := do
  let reply ← NFY_NBN_AfterstateDecoderDependency.run (fun b => ok (NFY_NBP_DigestDecode.decoded b)) bytes
  NGF_NEC_AfterstateBox.reference reply

/-- Reuse the composed child, with unchanged external state and empty runtime
trace. Native Box allocation and cleanup are checked separately under (aa). -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run bytes,state,([] : List Unit)) =
    (pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1 bytes,state,[]) := by
  exact congrArg (fun r => (r,state,([] : List Unit))) (NGF_NED_AfterBoxComposition.result bytes).symm

/-- The wrapper forwards the same slice. Its 688-byte child domain follows
from its own domain, with no inner-domain premise. -/
theorem child_packet (bytes : Array U8 688#usize) :
    bytes.to_slice.val.length = 688 := bytes.property

/-- Native projections quantify every scalar/limb/frontier entry. -/
theorem value_ext (a b : Value)
    (index : a.next_pair_index=b.next_pair_index)
    (root : ∀ i : Fin 8, NFY_NEU_PublicProjections.get a.next_root i = NFY_NEU_PublicProjections.get b.next_root i)
    (frontier : ∀ k : Fin 20, ∀ i : Fin 8,
      NFY_NEU_PublicProjections.get (NFY_NEU_PublicProjections.get a.next_frontier k) i =
      NFY_NEU_PublicProjections.get (NFY_NEU_PublicProjections.get b.next_frontier k) i) : a=b := by
  have hr := NFY_NED_WindowExtensionality.array_ext a.next_root b.next_root root
  have hf : a.next_frontier=b.next_frontier := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro k
    exact NFY_NED_WindowExtensionality.array_ext _ _ (frontier k)
  cases a
  cases b
  simp_all only

#print axioms result_state_effects
#print axioms child_packet
#print axioms value_ext
end NGF_NEX_AfterstateBox

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
