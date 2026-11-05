import NGL_MetaReference.Funs
import NIM_NGL_ErrorCarrier
import NGL_ArrayEquality
import NGL_ReadonlyModel
set_option autoImplicit false
noncomputable section
namespace NGL_MetaReferenceModel
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev Key := NGL_ReadonlyModel.Key

def port {T : Type} : core.result.Result T NGL_MetaReference.ProgramError →
    core.result.Result T AdapterRw.solana_program_error.ProgramError
  | .Ok v => .Ok v
  | .Err e => .Err (NGL_ErrorCarrier.from_meta e)

theorem comparison (a b : Key) :
    core.cmp.impls.PartialEqShared.ne
      (NGL_MetaReference.Array.Insts.CoreCmpPartialEqArray 32#usize core.cmp.PartialEqU8) a b =
      ok (!(decide (a = b))) := by
  change core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b = _
  exact NGL_ArrayEquality.ne_value a b

theorem source (ops : AdapterRw.Ops) (owner expected : Key) (s w e : Bool) :
    (do let r ← NGL_MetaReference.readonly_ref owner expected s w e
        ok (port r)) =
      AdapterRw.r1_pool_adapter.readonly_meta_ok
        (NGL_ReadonlyModel.install ops) owner expected s w e := by
  rw [NGL_ReadonlyModel.metadata_result]
  unfold NGL_MetaReference.readonly_ref
  rw [comparison]
  cases decide (owner = expected) <;> cases s <;> cases w <;> cases e <;> rfl
#print axioms comparison
#print axioms source
end NGL_MetaReferenceModel
