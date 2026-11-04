import Lean
import NGK_NFO_FlatMapInjective
import NGK_NFO_U64Roundtrip
import NFY_Part035
import RPz7_S6NativeAfterstateContentsV1

set_option autoImplicit false
namespace NGK_NFO_AfterstateInjective
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K AspisS6NativeAfterstateEncoderReuse
open AspisS6SourceCodec
abbrev Afterstate := pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

theorem injective (a b : Afterstate)
    (same : AfterstateEncoding.bytes a = AfterstateEncoding.bytes b) : a = b := by
  have content := congrArg (fun x : Array U8 688#usize => x.val) same
  rw [native_afterstate_contents,native_afterstate_contents] at content
  have headerWidth : header_bytes.length = 8 := by
    simp [header_bytes,pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property]
  have iw (x : U64) : (core.num.U64.to_le_bytes x).val.length = 8 := (core.num.U64.to_le_bytes x).property
  have dw (x : Array U32 8#usize) : (DigestContents.chunks x).length = 32 := PaymentContents.digest_chunks_length x
  have selectedIndex := congrArg (fun xs : List U8 => (xs.drop 8).take 8) content
  have hi : (core.num.U64.to_le_bytes a.next_pair_index).val = (core.num.U64.to_le_bytes b.next_pair_index).val := by
    simpa [prefix_bytes,List.append_assoc,List.drop_append,List.take_append,headerWidth,iw,dw] using selectedIndex
  have index : a.next_pair_index = b.next_pair_index := by
    have arrays : core.num.U64.to_le_bytes a.next_pair_index = core.num.U64.to_le_bytes b.next_pair_index := Subtype.ext hi
    simpa only [NGK_NFO_U64Roundtrip.from_to] using congrArg core.num.U64.from_le_bytes arrays
  have selectedRoot := congrArg (fun xs : List U8 => (xs.drop 16).take 32) content
  have rootBytes : DigestContents.chunks a.next_root = DigestContents.chunks b.next_root := by
    simpa [prefix_bytes,List.append_assoc,List.drop_append,List.take_append,headerWidth,iw,dw] using selectedRoot
  have root := AspisR1.NFY_JFt_DigestInjective.injective _ _ rootBytes
  have selectedFrontier := congrArg (List.drop 48) content
  have frontierBytes : a.next_frontier.val.flatMap DigestContents.chunks = b.next_frontier.val.flatMap DigestContents.chunks := by
    simpa [prefix_bytes,List.append_assoc,List.drop_append,headerWidth,iw,dw] using selectedFrontier
  have frontier : a.next_frontier = b.next_frontier := Subtype.ext
    (NGK_NFO_FlatMapInjective.uniform DigestContents.chunks 32 (by decide) dw
      (fun _ _ h => AspisR1.NFY_JFt_DigestInjective.injective _ _ h) frontierBytes)
  cases a
  cases b
  simp_all only
#print axioms injective
end NGK_NFO_AfterstateInjective

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
