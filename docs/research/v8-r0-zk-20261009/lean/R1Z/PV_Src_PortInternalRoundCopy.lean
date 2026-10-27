import R1Z.PV_Src_PortAddCopy
import R1Z.PV_Src_PortInternalCopy

/-! The actual internal-round body, including every source Result operation,
identifies the frozen modulo copy for canonical state and constant inputs. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalRoundCopy
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep

def run (s : State) (c : U32) : Result State := do
  let first ← Array.index_usize s 0#usize
  let added ← aspis_core.field.M31.add first c
  let powered ← poseidon2.pow5 added
  let changed ← Array.update s 0#usize powered
  poseidon2.internal_linear_lazy changed

theorem source (s : State) (c : U32) (hs : Canonical s) (hc : c.val < 2147483647) :
    run s c = R0PoseidonCopy.internal_round s c R0PoseidonCopy.INTERNAL_SHIFTS := by
  letI : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
  obtain ⟨a,ha,hca,_⟩ := PV_Src_PortField.addition (K := ZMod 2147483647)
    s.val[0]! c (hs ⟨0,by decide⟩) hc
  obtain ⟨b,hb,hcb,_⟩ := PV_Src_PortField.power (K := ZMod 2147483647) a
  have ha' : R0PoseidonCopy.m31_add s.val[0]! c = ok a := by
    rw [← PV_Src_PortAddCopy.source _ _ (hs ⟨0,by decide⟩) hc];exact ha
  have hb' : R0PoseidonCopy.pow5 a = ok b := by
    rw [← PV_Src_PortMultiply.power];exact hb
  rw [run,R0PoseidonCopy.internal_round]
  simp only [index_ok s 0#usize (by decide),bind_tc_ok,ha,ha',hb,hb',
    update_ok s 0#usize b (by decide),UScalar.ofNatCore_val_eq]
  exact PV_Src_PortInternalCopy.source (s.set 0#usize b)
    (canonical_set s 0#usize (by decide) b hcb hs)

#print axioms source
end R1Z.PV_Src_PortInternalRoundCopy
