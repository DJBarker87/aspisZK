import R1Z.PV_RE_DictSuffix000
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix001
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.Profile21SourceExpander.new`.
Recursive calls remain the original extracted calls. -/
def continueAfter (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (seed : Array Std.U8 32#usize) (out : Payload (zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) seed)) : Result aspis_prover.state_only_entropy.Profile21SourceExpander := do
  let z := out
  let a := Array.repeat 32#usize 0#u8
  ok { hash, seed := z, counter := 0#u64, block := a, word := 8#usize }


end R1Z.PV_RE_DictSuffix001
pv_dict_congr ProverRwFull.aspis_prover.state_only_entropy.Profile21SourceExpander.new
pv_dict_congr R1Z.PV_RE_DictSuffix001.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.aspis_prover.state_only_entropy.Profile21SourceExpander.new
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix001.continueAfter
