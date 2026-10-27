import JHb_CheckpointSize
import JGx_MagicStd
import JHb_Programs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHd_KeyStd
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
/-- Pure standard key/array operations, on every input. No ASQ8 acceptance,
PDA creation, account decoder or protocol-child return is installed here. -/
def keyEq (left right : solana_pubkey.Pubkey) : Result Bool :=
  core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 left right

def install (base : Ops) : Ops :=
  {JGx_MagicStd.install base with
    op9:=fun input=>ok input.val.head?
    op12:=JHb_CheckpointSize.value
    op36:=keyEq
    op37:=fun bytes=>ok bytes
    op39:=fun key=>ok key
    op40:=fun key=>ok key.to_slice
    op45:=ok JHb_Programs.pool
    op46:=ok JHb_Programs.registry}
#print axioms keyEq
#print axioms install
end AspisR1.JHd_KeyStd
end
