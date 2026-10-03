import AspisR519SharedGammaPartsV3.Funs
import AspisV8R19.R159WideBaseExecution
import AspisR515SharedGamma.SharedGammaDots

set_option autoImplicit false
namespace AspisV8R19.R529SelectedPartsExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
namespace New
abbrev M31 := AspisR519SharedGammaPartsV3.aspis_core.field.M31
abbrev CM31 := AspisR519SharedGammaPartsV3.aspis_core.field.CM31
abbrev QM31 := AspisR519SharedGammaPartsV3.aspis_core.field.QM31
end New

/-- Equality for every raw U32 input retains the guarded fallback branch. -/
theorem raw_add_eq (a b : U32) :
    AspisR519SharedGammaPartsV3.aspis_core.field.r91_raw_add a b =
      AspisR156FullFreeze.aspis_core.field.r91_raw_add a b := by
  simp only [AspisR519SharedGammaPartsV3.aspis_core.field.r91_raw_add,
    AspisR156FullFreeze.aspis_core.field.r91_raw_add, AspisR156FullFreeze.aspis_core.field.P]

theorem m31_add_eq (a b : U32) :
    AspisR519SharedGammaPartsV3.aspis_core.field.M31.add a b =
      AspisR156FullFreeze.aspis_core.field.M31.add a b := by
  have hmax : core.num.U32.MAX = (4294967295#u32 : U32) := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  simp only [AspisR519SharedGammaPartsV3.aspis_core.field.M31.add,
    AspisR156FullFreeze.aspis_core.field.M31.add, raw_add_eq,
    AspisR156FullFreeze.aspis_core.field.P, hmax]

def encodeInput (q : Fin 4 → M31Exact) : New.QM31 :=
  {c0 := {a := encodeBase (q 0), b := encodeBase (q 1)},
   c1 := {a := encodeBase (q 2), b := encodeBase (q 3)}}

def encodedParts (q : Fin 4 → M31Exact) : Array (Array U32 3#usize) 3#usize :=
  Array.make 3#usize [
    Array.make 3#usize [encodeBase (q 0),encodeBase (q 1),encodeBase (q 0+q 1)],
    Array.make 3#usize [encodeBase (q 2),encodeBase (q 3),encodeBase (q 2+q 3)],
    Array.make 3#usize [encodeBase (q 0+q 2),encodeBase (q 1+q 3),
      encodeBase ((q 0+q 2)+(q 1+q 3))]]

/-- Exact execution of the selected captured helper, including its five M31
additions and complete nine-entry array result, on encoded canonical inputs. -/
theorem selected_parts_encode (q : Fin 4 → M31Exact) :
    AspisR519SharedGammaPartsV3.r17_host_relation.shared_gamma.parts (encodeInput q) =
      .ok (encodedParts q) := by
  simp only [AspisR519SharedGammaPartsV3.r17_host_relation.shared_gamma.parts,
    AspisR519SharedGammaPartsV3.aspis_core.field.CM31.add, encodeInput,
    m31_add_eq, R159WideBaseExecution.add_encode, bind_tc_ok, encodedParts]

def canonical (v : New.QM31) : Prop :=
  v.c0.a.val<P ∧ v.c0.b.val<P ∧ v.c1.a.val<P ∧ v.c1.b.val<P

def decodeInput (v : New.QM31) : Fin 4 → M31Exact :=
  ![(v.c0.a.val : M31Exact), (v.c0.b.val : M31Exact),
    (v.c1.a.val : M31Exact), (v.c1.b.val : M31Exact)]

theorem encode_cast (a : U32) (h : a.val<P) : encodeBase (a.val : M31Exact) = a :=
  (ComplexBaseExecution.eq_encodeBase a _ h rfl).symm

theorem encode_decodeInput (v : New.QM31) (hc : canonical v) :
    encodeInput (decodeInput v) = v := by
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases hc with ⟨ha,hb,hc,hd⟩
  simp [encodeInput,decodeInput,encode_cast a ha,encode_cast b hb,
    encode_cast c hc,encode_cast d hd]

theorem selected_parts_canonical (v : New.QM31) (hc : canonical v) :
    AspisR519SharedGammaPartsV3.r17_host_relation.shared_gamma.parts v =
      .ok (encodedParts (decodeInput v)) := by
  conv_lhs => rw [← encode_decodeInput v hc]
  exact selected_parts_encode _

#print axioms raw_add_eq
#print axioms m31_add_eq
#print axioms selected_parts_encode
#print axioms encode_decodeInput
#print axioms selected_parts_canonical
end AspisV8R19.R529SelectedPartsExecution
