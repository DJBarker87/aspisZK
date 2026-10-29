import R1Z.PV_RunJoin_CircleOwnedScalar52
import R1Z.PV_RunJoin_CircleOwnedCarrier52
import R1Z.PV_RunJoin_CircleRawTower52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedTower52
open PV_RunJoin_CircleOwnedCarrier52
theorem t0 (self : CM) (other : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq (encCM self) (encCM other) = PV_RunJoin_CircleRawTower52.field.CM31.Insts.CoreCmpPartialEqCM31.eq self other := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq PV_RunJoin_CircleRawTower52.field.CM31.Insts.CoreCmpPartialEqCM31.eq
  simp only [PV_RunJoin_CircleOwnedScalar52.f7,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t1  :
    PV_AL_CircleOwned.aspis_core.field.CM31.ZERO  = encCM (PV_RunJoin_CircleRawTower52.field.CM31.ZERO ) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.ZERO PV_RunJoin_CircleRawTower52.field.CM31.ZERO
  simp only [bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t2  :
    PV_AL_CircleOwned.aspis_core.field.CM31.ONE  = encCM (PV_RunJoin_CircleRawTower52.field.CM31.ONE ) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.ONE PV_RunJoin_CircleRawTower52.field.CM31.ONE
  simp only [bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t3 (a : U32) (b : U32) :
    PV_AL_CircleOwned.aspis_core.field.CM31.new a b = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.new a b; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.new PV_RunJoin_CircleRawTower52.field.CM31.new
  simp only [bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t4 (self : CM) (rhs : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.add (encCM self) (encCM rhs) = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.add self rhs; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.add PV_RunJoin_CircleRawTower52.field.CM31.add
  simp only [PV_RunJoin_CircleOwnedScalar52.f14,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t5 (self : CM) (rhs : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.sub (encCM self) (encCM rhs) = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.sub self rhs; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.sub PV_RunJoin_CircleRawTower52.field.CM31.sub
  simp only [PV_RunJoin_CircleOwnedScalar52.f17,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t6 (self : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.neg (encCM self) = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.neg self; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.neg PV_RunJoin_CircleRawTower52.field.CM31.neg
  simp only [PV_RunJoin_CircleOwnedScalar52.f18,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t7 (self : CM) (rhs : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.mul (encCM self) (encCM rhs) = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.mul self rhs; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.mul PV_RunJoin_CircleRawTower52.field.CM31.mul
  simp only [PV_RunJoin_CircleOwnedScalar52.f9,PV_RunJoin_CircleOwnedScalar52.f13,PV_RunJoin_CircleOwnedScalar52.f17,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t8 (self : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.square (encCM self) = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.square self; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.square PV_RunJoin_CircleRawTower52.field.CM31.square
  simp only [PV_RunJoin_CircleOwnedScalar52.f0,PV_RunJoin_CircleOwnedScalar52.f9,PV_RunJoin_CircleOwnedScalar52.f13,PV_RunJoin_CircleOwnedScalar52.f15,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t9 (self : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.double (encCM self) = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.double self; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.double PV_RunJoin_CircleRawTower52.field.CM31.double
  simp only [t4,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t10 (self : CM)
  (inverse : U32 → Result U32) :
    PV_AL_CircleOwned.aspis_core.field.CM31.inv_with (encCM self) inverse = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.inv_with self inverse; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.inv_with PV_RunJoin_CircleRawTower52.field.CM31.inv_with
  simp only [PV_RunJoin_CircleOwnedScalar52.f9,PV_RunJoin_CircleOwnedScalar52.f14,PV_RunJoin_CircleOwnedScalar52.f18,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t11 (self : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.inv (encCM self) = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.inv self; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.inv PV_RunJoin_CircleRawTower52.field.CM31.inv
  simp only [t10,PV_RunJoin_CircleOwnedScalar52.f16,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t12 (x : CM) :
    PV_AL_CircleOwned.aspis_core.field.mul_by_r (encCM x) = (do let x ← PV_RunJoin_CircleRawTower52.field.mul_by_r x; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.mul_by_r PV_RunJoin_CircleRawTower52.field.mul_by_r
  simp only [PV_RunJoin_CircleOwnedScalar52.f14,PV_RunJoin_CircleOwnedScalar52.f15,PV_RunJoin_CircleOwnedScalar52.f17,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t13  :
    PV_AL_CircleOwned.aspis_core.field.QM31.ZERO  = encQ (PV_RunJoin_CircleRawTower52.field.QM31.ZERO ) := by
  unfold PV_AL_CircleOwned.aspis_core.field.QM31.ZERO PV_RunJoin_CircleRawTower52.field.QM31.ZERO
  simp only [bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t14  :
    PV_AL_CircleOwned.aspis_core.field.QM31.ONE  = encQ (PV_RunJoin_CircleRawTower52.field.QM31.ONE ) := by
  unfold PV_AL_CircleOwned.aspis_core.field.QM31.ONE PV_RunJoin_CircleRawTower52.field.QM31.ONE
  simp only [bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t15 (self : Q) (rhs : Q) :
    PV_AL_CircleOwned.aspis_core.field.QM31.add (encQ self) (encQ rhs) = (do let x ← PV_RunJoin_CircleRawTower52.field.QM31.add self rhs; ok (encQ x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.QM31.add PV_RunJoin_CircleRawTower52.field.QM31.add
  simp only [t4,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t16 (self : Q) (rhs : Q) :
    PV_AL_CircleOwned.aspis_core.field.QM31.sub (encQ self) (encQ rhs) = (do let x ← PV_RunJoin_CircleRawTower52.field.QM31.sub self rhs; ok (encQ x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.QM31.sub PV_RunJoin_CircleRawTower52.field.QM31.sub
  simp only [t5,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t17 (self : Q) (rhs : Q) :
    PV_AL_CircleOwned.aspis_core.field.QM31.mul (encQ self) (encQ rhs) = (do let x ← PV_RunJoin_CircleRawTower52.field.QM31.mul self rhs; ok (encQ x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.QM31.mul PV_RunJoin_CircleRawTower52.field.QM31.mul
  simp only [t4,t5,t7,t12,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t18 (self : Q) :
    PV_AL_CircleOwned.aspis_core.field.QM31.square (encQ self) = (do let x ← PV_RunJoin_CircleRawTower52.field.QM31.square self; ok (encQ x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.QM31.square PV_RunJoin_CircleRawTower52.field.QM31.square
  simp only [t4,t7,t8,t9,t12,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t19 (self : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.is_zero (encCM self) = PV_RunJoin_CircleRawTower52.field.CM31.is_zero self := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.is_zero PV_RunJoin_CircleRawTower52.field.CM31.is_zero
  simp only [PV_RunJoin_CircleOwnedScalar52.f19,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t20 (self : Q) :
    PV_AL_CircleOwned.aspis_core.field.QM31.is_zero (encQ self) = PV_RunJoin_CircleRawTower52.field.QM31.is_zero self := by
  unfold PV_AL_CircleOwned.aspis_core.field.QM31.is_zero PV_RunJoin_CircleRawTower52.field.QM31.is_zero
  simp only [t19,bind_assoc_eq,bind_tc_ok,encCM,encQ]

theorem t21 (self : Q) :
    PV_AL_CircleOwned.aspis_core.field.QM31.try_inv (encQ self) = (do let x ← PV_RunJoin_CircleRawTower52.field.QM31.try_inv self; ok ((Option.map encQ) x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.QM31.try_inv PV_RunJoin_CircleRawTower52.field.QM31.try_inv
  simp only [t5,t6,t7,t8,t11,t12,t20,bind_assoc_eq,bind_tc_ok,encCM,encQ]


#print axioms t0
#print axioms t1
#print axioms t2
#print axioms t3
#print axioms t4
#print axioms t5
#print axioms t6
#print axioms t7
#print axioms t8
#print axioms t9
#print axioms t10
#print axioms t11
#print axioms t12
#print axioms t13
#print axioms t14
#print axioms t15
#print axioms t16
#print axioms t17
#print axioms t18
#print axioms t19
#print axioms t20
#print axioms t21
end R1Z.PV_RunJoin_CircleOwnedTower52
