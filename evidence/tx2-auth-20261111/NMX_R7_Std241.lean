import NMX_R4_CallContext
import NMX_R7_Verify241
set_option autoImplicit false
noncomputable section
namespace NMX_R7_Std241
open Aeneas Aeneas.Std Result AdapterRw

def optionEq {T : Type} (cmp : core.cmp.PartialEq T T) (x y : Option T) : Result Bool :=
 match x,y with
 | none,none => ok true
 | some a,some b => cmp.eq a b
 | _,_ => ok false

def ops (env : RSL.Env) : Ops :=
 {NMX_R2_StdOps.install env false .panic with
  op2 := optionEq
  op4 := fun _ slice => ok slice
  op42 := fun value => ok value
  op43 := fun _ parts => ok (NMX_R2_InverseBytes.fromKey (env.sha256 (parts.val.map NMX_R2_Carrier.bytes)))}

theorem observer (env : RSL.Env) : AdapterRw.observer (ops env) = ok none := rfl

theorem full_range (env : RSL.Env) (T : Type) (a : Slice T) :
 (ops env).op4 () a = ok a := rfl

theorem digest (env : RSL.Env) (parts : Slice (Slice U8)) :
 (SolanaDigest.Insts.Aspis_coreDigestDigest32 (ops env)).digest () parts =
 ok (NMX_R2_InverseBytes.fromKey (env.sha256 (parts.val.map NMX_R2_Carrier.bytes))) := rfl

#print axioms observer
#print axioms full_range
#print axioms digest
end NMX_R7_Std241
end
