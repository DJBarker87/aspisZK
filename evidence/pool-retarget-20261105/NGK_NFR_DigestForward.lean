import Lean
import NGK_NFR_RawInverseHelpers
import NFY_Part005

set_option autoImplicit false
noncomputable section
namespace NGK_NFR_DigestForward
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K
theorem four_eta (a : Array U8 4#usize) :
    Array.make 4#usize
      [a.val[0]'(by rw [a.property]; decide),a.val[1]'(by rw [a.property]; decide),
       a.val[2]'(by rw [a.property]; decide),a.val[3]'(by rw [a.property]; decide)] = a := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [Array.make,a.property]
  · intro i hi hj
    have small : i < 4 := by simpa only [a.property,show (4#usize).val = 4 from rfl] using hj
    interval_cases i <;> rfl
#print axioms four_eta

theorem eight_eta (a : Array U32 8#usize) :
    Array.make 8#usize [a.val[0]'(by rw [a.property]; decide),a.val[1]'(by rw [a.property]; decide),a.val[2]'(by rw [a.property]; decide),a.val[3]'(by rw [a.property]; decide),a.val[4]'(by rw [a.property]; decide),a.val[5]'(by rw [a.property]; decide),a.val[6]'(by rw [a.property]; decide),a.val[7]'(by rw [a.property]; decide)] = a := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [Array.make,a.property]
  · intro i hi hj
    have small : i < 8 := by simpa only [a.property,show (8#usize).val = 8 from rfl] using hj
    interval_cases i <;> rfl
#print axioms eight_eta

theorem roundtrip (digest : Array U32 8#usize) (canonical : NBD_DigestInduction.Canonical digest) :
    atomic_statement.decode_digest_canonical (DigestBytes.bytes digest) = ok (.Ok digest) := by
  have encoded : (DigestBytes.bytes digest).val = AspisS6SourceCodec.DigestContents.chunks digest :=
    AspisS6NativeAfterstateEncoderReuse.native_digest_bytes digest
  have word_length (x : U32) : (core.num.U32.to_le_bytes x).val.length = 4 :=
    (core.num.U32.to_le_bytes x).property
  have h0 := canonical ⟨0,by decide⟩
  have h1 := canonical ⟨1,by decide⟩
  have h2 := canonical ⟨2,by decide⟩
  have h3 := canonical ⟨3,by decide⟩
  have h4 := canonical ⟨4,by decide⟩
  have h5 := canonical ⟨5,by decide⟩
  have h6 := canonical ⟨6,by decide⟩
  have h7 := canonical ⟨7,by decide⟩
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    (DigestBytes.bytes digest).property,encoded,AspisS6SourceCodec.DigestContents.chunks,
    word_length,List.getElem_append,four_eta,
    aspis_core.field.M31.from_le_bytes,AspisR1.NFY_JFt_DigestInjective.from_to,
    aspis_core.field.P,core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,lift,h0.not_ge,h1.not_ge,h2.not_ge,h3.not_ge,
    h4.not_ge,h5.not_ge,h6.not_ge,h7.not_ge,eight_eta]
#print axioms roundtrip
end NGK_NFR_DigestForward

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
