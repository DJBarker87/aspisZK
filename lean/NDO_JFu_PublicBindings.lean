import NDO_JFu_PublicMeta02
import NDO_JFu_PublicMeta03
set_option autoImplicit false
namespace AspisR1.JFu_PublicBindings
open Aeneas Aeneas.Std Result

def pool : Array U8 32#usize := ⟨JFu_PublicMeta02.bytes,JFu_PublicMeta02.length⟩
def domain : Array U8 32#usize := ⟨JFu_PublicMeta03.bytes,JFu_PublicMeta03.length⟩

theorem pool_selected : (JFx_NativeBytes.publicInput.val.drop 224).take 32=pool.val :=
  JFu_PublicMeta02.selected

theorem domain_selected : (JFx_NativeBytes.publicInput.val.drop 256).take 32=domain.val :=
  JFu_PublicMeta03.selected

/-- The source comparison short-circuits on the first unequal byte,34 versus0. -/
theorem pool_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    pool (Array.repeat 32#usize 0#u8)=ok false := by rfl

/-- The source comparison short-circuits on the first unequal byte,5 versus0. -/
theorem domain_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    domain (Array.repeat 32#usize 0#u8)=ok false := by rfl

#print axioms pool_selected
#print axioms domain_selected
#print axioms pool_nonzero
#print axioms domain_nonzero
end AspisR1.JFu_PublicBindings
