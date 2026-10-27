import KSA_Checks
open Aeneas Aeneas.Std Result XRn_Join_Release XRn_Join_FieldExternal
set_option autoImplicit false
namespace KSA.Small

def two : aspis_core.field.QM31 := ⟨⟨2#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def three : aspis_core.field.QM31 := ⟨⟨3#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def four : aspis_core.field.QM31 := ⟨⟨4#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def wz : XRn_Join_Wide := ⟨oldQ qzero,oldQ qzero⟩
def wo : XRn_Join_Wide := ⟨oldQ qone,oldQ qzero⟩
def wt : XRn_Join_Wide := ⟨oldQ two,oldQ qzero⟩

theorem p : aspis_core.field.P = ok 2147483647#u32 := by rfl
theorem zero : aspis_core.field.M31.ZERO = ok 0#u32 := by rfl
theorem one : aspis_core.field.M31.ONE = ok 1#u32 := by rfl
theorem clone : aspis_core.field.M31.Insts.CoreCloneClone.clone 2#u32 = ok 2#u32 := by rfl
theorem eq : aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq 2#u32 2#u32 = ok true := by rfl
theorem add : XRn_Join_Field.field.M31.add 1#u32 2#u32 = ok 3#u32 := by rfl
theorem sub : aspis_core.field.M31.sub 2#u32 1#u32 = ok 1#u32 := by rfl
theorem mul : aspis_core.field.M31.mul 2#u32 2#u32 = ok 4#u32 := by rfl
theorem double : aspis_core.field.M31.double 2#u32 = ok 4#u32 := by rfl
theorem reduce : aspis_core.field.M31.reduce_u64 2147483648#u64 = ok 1#u32 := by rfl
theorem cm_new : aspis_core.field.CM31.new 1#u32 2#u32 = ok ⟨1#u32,2#u32⟩ := by rfl
theorem cm_mul : aspis_core.field.CM31.mul ⟨1#u32,0#u32⟩ ⟨2#u32,0#u32⟩ = ok ⟨2#u32,0#u32⟩ := by rfl
theorem q_clone : aspis_core.field.QM31.Insts.CoreCloneClone.clone two = ok two := by rfl
theorem q_ne : aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne two three = ok true := by rfl
theorem q_zero : aspis_core.field.QM31.ZERO = ok qzero := by rfl
theorem q_one : aspis_core.field.QM31.ONE = ok qone := by rfl
theorem q_add : aspis_core.field.QM31.add two qone = ok three := by rfl
theorem q_mul : aspis_core.field.QM31.mul two two = ok four := by rfl
theorem canonical : canon two = ok two := by rfl
theorem w_zero : aspis_core.field.wide_exact.WideExact.ZERO = ok wz := by rfl
theorem w_one : aspis_core.field.wide_exact.WideExact.ONE = ok wo := by rfl
theorem w_new : aspis_core.field.wide_exact.WideExact.new qone qzero = ok wo := by rfl
theorem w_from : aspis_core.field.wide_exact.WideExact.from_qm31 qone = ok wo := by rfl
theorem w_ne : aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.ne wo wz = ok true := by rfl
theorem w_add : aspis_core.field.wide_exact.WideExact.add wo wo = ok wt := by rfl
theorem w_sub : aspis_core.field.wide_exact.WideExact.sub wt wo = ok wo := by rfl
theorem w_mul : aspis_core.field.wide_exact.WideExact.mul wt wo = ok wt := by rfl
theorem w_mulq : aspis_core.field.wide_exact.WideExact.mul_qm31 wo two = ok wt := by rfl
theorem w_mulm : aspis_core.field.wide_exact.WideExact.mul_m31 wo 2#u32 = ok wt := by rfl
theorem fibre_new : aspis_core.r0.domain.FibreIndex.new 262144#usize = ok (.Err .IndexOutOfRange) := by rfl
theorem fibre_get : aspis_core.r0.domain.FibreIndex.get 2#usize = ok 2#usize := by rfl
theorem c1_tag : aspis_core.r0.merkle.C1_TAG = ok 113#u8 := by rfl
theorem c2_tag : aspis_core.r0.merkle.C2_TAG = ok 241#u8 := by rfl

#print axioms p
#print axioms zero
#print axioms one
#print axioms clone
#print axioms eq
#print axioms add
#print axioms sub
#print axioms mul
#print axioms double
#print axioms reduce
#print axioms cm_new
#print axioms cm_mul
#print axioms q_clone
#print axioms q_ne
#print axioms q_zero
#print axioms q_one
#print axioms q_add
#print axioms q_mul
#print axioms canonical
#print axioms w_zero
#print axioms w_one
#print axioms w_new
#print axioms w_from
#print axioms w_ne
#print axioms w_add
#print axioms w_sub
#print axioms w_mul
#print axioms w_mulq
#print axioms w_mulm
#print axioms fibre_new
#print axioms fibre_get
#print axioms c1_tag
#print axioms c2_tag
end KSA.Small
