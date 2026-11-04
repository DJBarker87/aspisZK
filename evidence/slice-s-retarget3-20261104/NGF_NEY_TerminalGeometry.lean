import Lean
import NGF_NEX_TerminalDomain
import NGF_NEX_DecoderDomains

set_option autoImplicit false
noncomputable section
namespace NGF_NEY_TerminalGeometry
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

theorem payment_offset : PAYMENT_STATEMENT_OFFSET=ok 1664#usize := by
  obtain ⟨n,run,value⟩ := spec_imp_exists AspisS6NativeForestDecodeHelpers.payment_offset_spec
  have same : n=1664#usize := by scalar_tac
  simpa only [same] using run

#print AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION

theorem header_constants :
    POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val=[65#u8,83#u8,70#u8,56#u8] ∧
    POOL_V1_PAIR_FOREST_TERMINAL_VERSION=1#u8 ∧
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION=1#u8 := by
  constructor
  · unfold POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC
    rfl
  constructor
  · unfold POOL_V1_PAIR_FOREST_TERMINAL_VERSION
    rfl
  · unfold AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
    rfl

/-- The actual extracted successful kind call chooses the SAME payment branch. -/
theorem kind_same (byte : U8) (kind : pool_v1.historical_anchor.PoolV1TransitionKind)
    (accepted : transition_kind byte=ok (.Ok kind)) :
    (read_discriminant kind : U8)=byte := by
  obtain ⟨r,run,value⟩ := spec_imp_exists (AspisS6NativeForestDecodeHelpers.kind_spec byte)
  have same : r=.Ok kind := Result.ok.inj (run.symm.trans accepted)
  exact value kind same

/-- The real model offset, not an independent literal window, supplies216 bytes. -/
theorem payment_window (bytes : Array U8 1880#usize) :
    (do let offset ← PAYMENT_STATEMENT_OFFSET
        ok (bytes.val.drop offset.val).length) = ok 216 := by
  rw [payment_offset]
  simp only [bind_tc_ok,List.length_drop,bytes.property]
  rfl

#print axioms payment_offset
#print axioms header_constants
#print axioms kind_same
#print axioms payment_window
end NGF_NEY_TerminalGeometry

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
