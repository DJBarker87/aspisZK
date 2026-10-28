import JHd_KeyStd
import NDO_JFp_SHADigest
import RPz7_S6NativeAfterstateCodecV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_SdkLeaves
open Aeneas Aeneas.Std Result

def sliceNe {T U : Type} {n : Usize} (cmp : core.cmp.PartialEq T U)
    (left : Slice T) (right : Array U n) : Result Bool :=
  core.slice.cmp.PartialEqSlice.ne cmp left right.to_slice

def sliceArrayEq {T U : Type} {n : Usize} (cmp : core.cmp.PartialEq T U)
    (left : Slice T) (right : Array U n) : Result Bool :=
  core.slice.cmp.PartialEqSlice.eq cmp left right.to_slice

def validate (s : AspisS6CurrentCodecInstallation.Statement) :=
  AspisS6OuterNativeOps.resultMap
    (AspisS6CurrentCodecInstallation.mapBoth id
      AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalFormatErrorV1)
    (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 s))

def afterstate (s : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :=
  AspisS6OuterNativeOps.resultMap
    (AspisS6CurrentCodecInstallation.mapBoth id
      AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifierTransportErrorV1)
    (AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
      (AspisS6CurrentAdapterCarrier.toPoolV1PairVerifiedAfterstateV1 s))

/-- Pure leaves retain all source inputs; decode, validation, encode and
verifier children are installed by the concrete SDK installation separately. -/
def install (base : AdapterRw.Ops) : AdapterRw.Ops :=
  {JHd_KeyStd.install base with
    op21:=validate
    op24:=afterstate
    op0:=sliceNe
    op1:=sliceArrayEq
    op42:=fun x=>ok x
    op43:=S2W_DigestExtraction.digest (F3U_Oracle.hashv JFp_SHADigest.digest)}
end AspisR1.JHe_SdkLeaves
end
