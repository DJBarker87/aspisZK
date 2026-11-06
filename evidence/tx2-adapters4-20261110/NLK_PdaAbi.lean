import NLA_PdaStatus
set_option autoImplicit false
namespace NLK_PdaAbi
open Aeneas Aeneas.Std Result
abbrev Byte := U8
abbrev Key := NLA_PdaStatus.Key
/-- Ordered ABI observation: each descriptor selects the SAME seed occurrence;
program and reply are bytes at this call, never a PDA value law. -/
structure Input where
  seeds : List (List Byte)
  program : Fin 32 → Byte

def WindowEq (a b : Input) : Prop :=
  a.seeds.length=b.seeds.length ∧
  (∀ i, ∀ ha : i<a.seeds.length, ∀ hb : i<b.seeds.length,
    (a.seeds[i]'ha).length=(b.seeds[i]'hb).length ∧
    ∀ j, ∀ hja : j<(a.seeds[i]'ha).length, ∀ hjb : j<(b.seeds[i]'hb).length,
    (a.seeds[i]'ha)[j]'hja=(b.seeds[i]'hb)[j]'hjb) ∧
  ∀ j, a.program j=b.program j

theorem complete_input (a b : Input) (cut : WindowEq a b) : a=b := by
  have seeds : a.seeds=b.seeds := by
    apply List.ext_getElem cut.1
    intro i ha hb
    apply List.ext_getElem (cut.2.1 i ha hb).1
    intro j hja hjb
    exact (cut.2.1 i ha hb).2 j hja hjb
  have program : a.program=b.program := funext cut.2.2
  cases a; cases b
  cases seeds; cases program; rfl

/-- All statuses retain their exact SDK conversion. Unsupported statuses abort
before the caller's map_err/comparison. op38's output remains quantified. -/
def forward (panic : Error) (status : U64) (output : Key) :=
  NKF_PdaModel.continuation (NLA_PdaStatus.reply panic status output)

theorem returned_reply (panic : Error) (output : Key) :
  forward panic 0#u64 output = ok (.Ok output) := rfl

theorem error_one (panic : Error) (output : Key) :
  forward panic 1#u64 output = ok (.Err .InvalidAccountData) := rfl

theorem error_two (panic : Error) (output : Key) :
  forward panic 2#u64 output = ok (.Err .InvalidAccountData) := rfl

theorem unsupported (panic : Error) (status : U64) (output : Key)
    (large : 2<status.val) : forward panic status output = .fail panic :=
  NLA_PdaStatus.unsupported_prefix panic status output large

#print complete_input
#print axioms complete_input
#print axioms returned_reply
#print axioms error_one
#print axioms error_two
#print axioms unsupported
end NLK_PdaAbi
