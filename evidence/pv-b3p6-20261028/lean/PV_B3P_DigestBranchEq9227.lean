import PV_B3P_DigestCpsEq9227
import PV_B3P_DigestStage02227
import PV_B3P_Ordered227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227 PV_B3P_Ordered227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227

theorem recipient_stage_action9 {β : Type} (p : reference_terminal.SemanticPublic)
    (opened : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : DigestQ)
    (f : DigestQ → Result β) :
    (digest_stage_02 p opened selectors output >>= f) =
      recipient_action9 p.recipient output opened.z selectors f := by
  cases hr : p.recipient <;>
    simp only [digest_stage_02,recipient_action9,hr,bind_assoc,bind_tc_ok]

def frontier_primitive9 (output : DigestQ) (opened : Array aspis_core.field.QM31 16#usize)
    (selectors : reference_copy_terminal.Selectors) (frontier : FrontierM)
    (level block : Usize) (bit : U64) : Result DigestQ :=
  if bit=0#u64 then do
    let row ← lift (Usize.wrapping_mul block 16#usize)
    let selector ← reference_copy_terminal.Selectors.row selectors row
    let expected ← reference_terminal.empty_root level
    reference_terminal.add_digest_binding output selector opened aspis_statement.poseidon2.RATE expected true
  else do
    let base ← lift (Usize.wrapping_mul block 16#usize)
    let row ← lift (Usize.wrapping_add base 12#usize)
    let selector ← reference_copy_terminal.Selectors.row selectors row
    let expected ← reference_terminal.digest227 frontier level
    reference_terminal.add_digest_binding output selector opened 0#usize expected false

theorem frontier_primitive_bind9 {β : Type} (output : DigestQ)
    (opened : Array aspis_core.field.QM31 16#usize)
    (selectors : reference_copy_terminal.Selectors) (frontier : FrontierM)
    (level block : Usize) (bit : U64) (f : DigestQ → Result β) :
    (frontier_primitive9 output opened selectors frontier level block bit >>= f) =
      frontier_action9 output opened selectors frontier level block bit f := by
  by_cases h : bit=0#u64 <;>
    simp only [frontier_primitive9,frontier_action9,h,↓reduceIte,bind_assoc]

#print axioms recipient_stage_action9
#print axioms frontier_primitive_bind9
end PV_B3P_Binding9227
