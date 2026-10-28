import R1Z.ProverRwFullTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace R1Z.ProverRwDictionaryDerivedSource

def aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : aspis_core.field.M31) (other : aspis_core.field.M31) :
  Result Bool
  := do
  ok (self = other)

def aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq
  (self : aspis_core.field.CM31) (other : aspis_core.field.CM31) :
  Result Bool
  := do
  let b ← aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq self.a other.a
  if b
  then aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq self.b other.b
  else ok false

def aspis_core.field.QM31.Insts.CoreCloneClone.clone
  (self : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  ok self

def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
  (self : aspis_core.field.QM31) (other : aspis_core.field.QM31) :
  Result Bool
  := do
  let b ←
    aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq self.c0 other.c0
  if b
  then aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq self.c1 other.c1
  else ok false

end R1Z.ProverRwDictionaryDerivedSource
