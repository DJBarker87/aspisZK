import M31SquareSourceModel

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1M31Inverse.SquareProof
open R17CurrentM31Semantics

private theorem mul_power (mul : Mul) (href : RefinesMul mul)
    (x a b z : U32) (m n : Nat) (ha : decode a = decode x ^ m)
    (hb : decode b = decode x ^ n) (h : mul a b = .ok z) :
    decode z = decode x ^ (m+n) := by rw [href a b z h,ha,hb,pow_add]

private theorem square_power (mul : Mul) (ht : TotalMul mul)
    (hr : RefinesMul mul) (x a : U32) (e : Nat) (c : Usize)
    (ha : decode a = decode x ^ e) :
    ∃ z, field.square_n mul a c = .ok z ∧ decode z = decode x ^ (e*2^c.val) := by
  obtain ⟨z,hz,hv⟩ := square_n_total_model mul ht hr a c
  exact ⟨z,hz,by rw [hv,ha,pow_mul]⟩

theorem inv_total_power (mul : Mul) (ht : TotalMul mul) (hr : RefinesMul mul)
    (x : U32) (hx : x != 0#u32) :
    ∃ z, field.M31.inv mul x = .ok z ∧ decode z = decode x ^ 2147483645 := by
  have hxpow : decode x = decode x ^ 1 := (pow_one _).symm
  obtain ⟨m,h_m⟩ := ht x x
  have hp_m : decode m = decode x ^ 2 :=
    mul_power mul hr x x x m 1 1 hxpow hxpow h_m
  obtain ⟨t2,h_t2⟩ := ht m x
  have hp_t2 : decode t2 = decode x ^ 3 :=
    mul_power mul hr x m x t2 2 1 hp_m hxpow h_t2
  obtain ⟨m1,h_m1,hp_m1⟩ := square_power mul ht hr x t2 3 2#usize hp_t2
  obtain ⟨t4,h_t4⟩ := ht m1 t2
  have hp_t4 : decode t4 = decode x ^ 15 :=
    mul_power mul hr x m1 t2 t4 12 3 hp_m1 hp_t2 h_t4
  obtain ⟨m2,h_m2,hp_m2⟩ := square_power mul ht hr x t4 15 4#usize hp_t4
  obtain ⟨t8,h_t8⟩ := ht m2 t4
  have hp_t8 : decode t8 = decode x ^ 255 :=
    mul_power mul hr x m2 t4 t8 240 15 hp_m2 hp_t4 h_t8
  obtain ⟨m3,h_m3,hp_m3⟩ := square_power mul ht hr x t8 255 8#usize hp_t8
  obtain ⟨t16,h_t16⟩ := ht m3 t8
  have hp_t16 : decode t16 = decode x ^ 65535 :=
    mul_power mul hr x m3 t8 t16 65280 255 hp_m3 hp_t8 h_t16
  obtain ⟨m4,h_m4,hp_m4⟩ := square_power mul ht hr x t16 65535 8#usize hp_t16
  obtain ⟨t24,h_t24⟩ := ht m4 t8
  have hp_t24 : decode t24 = decode x ^ 16777215 :=
    mul_power mul hr x m4 t8 t24 16776960 255 hp_m4 hp_t8 h_t24
  obtain ⟨m5,h_m5,hp_m5⟩ := square_power mul ht hr x t24 16777215 4#usize hp_t24
  obtain ⟨t28,h_t28⟩ := ht m5 t4
  have hp_t28 : decode t28 = decode x ^ 268435455 :=
    mul_power mul hr x m5 t4 t28 268435440 15 hp_m5 hp_t4 h_t28
  obtain ⟨m6,h_m6⟩ := ht t28 t28
  have hp_m6 : decode m6 = decode x ^ 536870910 :=
    mul_power mul hr x t28 t28 m6 268435455 268435455 hp_t28 hp_t28 h_m6
  obtain ⟨t29,h_t29⟩ := ht m6 x
  have hp_t29 : decode t29 = decode x ^ 536870911 :=
    mul_power mul hr x m6 x t29 536870910 1 hp_m6 hxpow h_t29
  obtain ⟨t30,h_t30⟩ := ht t29 t29
  have hp_t30 : decode t30 = decode x ^ 1073741822 :=
    mul_power mul hr x t29 t29 t30 536870911 536870911 hp_t29 hp_t29 h_t30
  obtain ⟨m7,h_m7⟩ := ht t30 t30
  have hp_m7 : decode m7 = decode x ^ 2147483644 :=
    mul_power mul hr x t30 t30 m7 1073741822 1073741822 hp_t30 hp_t30 h_m7
  obtain ⟨z,h_z⟩ := ht m7 x
  have hp_z : decode z = decode x ^ 2147483645 :=
    mul_power mul hr x m7 x z 2147483644 1 hp_m7 hxpow h_z
  refine ⟨z,?_,hp_z⟩
  unfold field.M31.inv
  simp only [hx, massert, Bool.true_eq, ite_true, bind_tc_ok, h_m, h_t2, h_m1, h_t4, h_m2, h_t8, h_m3, h_t16, h_m4, h_t24, h_m5, h_t28, h_m6, h_t29, h_t30, h_m7, h_z]

theorem current_mul_total : TotalMul AspisR1Qm31ArithmeticProbe.field.M31.mul := by
  intro a b
  obtain ⟨z,hz,_,_⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod a b
  exact ⟨z,hz⟩

theorem current_inv_total_power (x : U32) (hx : x != 0#u32) :
    ∃ z, field.M31.inv AspisR1Qm31ArithmeticProbe.field.M31.mul x = .ok z ∧
      decode z = decode x ^ 2147483645 :=
  inv_total_power _ current_mul_total current_mul_decode x hx

#print axioms inv_total_power
#print axioms current_mul_total
#print axioms current_inv_total_power
end AspisR1M31Inverse.SquareProof
