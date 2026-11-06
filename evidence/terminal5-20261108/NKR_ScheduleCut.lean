import NKI_ScheduleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_ScheduleCut
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public Openings Selectors)
/-- NKR_schedule_cut: frozen add_schedule_lanes three-call transcription.
All child replies are arbitrary complete16/16 and24 arrays in the native
window. Exact SAME public/openings/selectors, both starts, both before/after
states and values, final output, read-only frames and call order are observed.
The native certificate and source SHA are listed in NKR_CERTIFICATES.md. -/
structure Observations where
 publicArg : Public
 openingArg : Openings
 selectorArg : Selectors
 firstBefore : Array NQ 24#usize
 secondBefore : Array NQ 24#usize
 values0 : Array NQ 16#usize
 values1 : Array NQ 16#usize
 firstAfter : Array NQ 24#usize
 secondAfter : Array NQ 24#usize
 returned : Array NQ 24#usize
 order : List Nat
 starts : Nat × Nat

def Cut (packed : Array NQ 24#usize) (p : Public) (o : Openings) (s : Selectors)
 (initial absorption : Array NQ 16#usize) (middle out : Array NQ 24#usize)
 (ob : Observations) : Prop :=
 ob.publicArg=p ∧ ob.openingArg=o ∧ ob.selectorArg=s ∧
 ob.firstBefore=packed ∧ ob.secondBefore=middle ∧
 ob.values0=initial ∧ ob.values1=absorption ∧
 ob.firstAfter=middle ∧ ob.secondAfter=out ∧ ob.returned=out ∧
 ob.order=[260,230,230] ∧ ob.starts=(0,16)

def observations (packed : Array NQ 24#usize) (p : Public) (o : Openings) (s : Selectors)
 (initial absorption : Array NQ 16#usize) (middle out : Array NQ 24#usize) : Observations :=
 ⟨p,o,s,packed,middle,initial,absorption,middle,out,out,[260,230,230],(0,16)⟩

theorem source (packed : Array NQ 24#usize) (p : Public) (o : Openings) (s : Selectors)
 (initial absorption : Array NQ 16#usize) (middle out : Array NQ 24#usize) :
 Cut packed p o s initial absorption middle out (observations packed p o s initial absorption middle out) :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms source
end AspisR1.NKR_ScheduleCut
end
