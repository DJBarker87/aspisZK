import PCG_AddressRef.Funs
import NGK_NFV_RequestGuards
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_AddressLaws
open PCG_AddressRef

def DescriptorDomain (q : Request) : Prop :=
 q.count.val ≤ 4 ∧ ∀ n ∈ q.lengths.val, n.val ≤ 32

def model_374
(program : Array Std.U8 32#usize) (pool : Array Std.U8 32#usize)
  (profile : Array Std.U8 32#usize) (release : Array Std.U8 32#usize) :
  Request
  :=
  {
      program,
      seeds :=
        (Array.make 4#usize [
          Array.make 32#usize [
            97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 118#u8, 101#u8,
            114#u8, 105#u8, 102#u8, 105#u8, 101#u8, 114#u8, 45#u8, 101#u8,
            110#u8, 116#u8, 114#u8, 121#u8, 45#u8, 118#u8, 49#u8, 0#u8, 0#u8,
            0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ], pool, profile, release
          ]),
      lengths :=
        (Array.make 4#usize [ 23#usize, 32#usize, 32#usize, 32#usize ]),
      count := 4#usize
    }

theorem request_374 (program pool : Array U8 32#usize) (profile release : Array U8 32#usize) :
 PCG_AddressRef.request_374 program pool profile release = ok (model_374 program pool profile release) := by rfl

theorem domain_374 (program pool : Array U8 32#usize) (profile release : Array U8 32#usize) :
 DescriptorDomain (model_374 program pool profile release) := by
 simp [DescriptorDomain,model_374,Array.make]

#print axioms request_374
#print axioms domain_374

def model_375
(program : Array Std.U8 32#usize) (pool : Array Std.U8 32#usize)
  (profile : Array Std.U8 32#usize) (release : Array Std.U8 32#usize) :
  Request
  :=
  {
      program,
      seeds :=
        (Array.make 4#usize [
          Array.make 32#usize [
            97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 118#u8, 101#u8,
            114#u8, 105#u8, 102#u8, 105#u8, 101#u8, 114#u8, 45#u8, 101#u8,
            110#u8, 116#u8, 114#u8, 121#u8, 45#u8, 118#u8, 50#u8, 0#u8, 0#u8,
            0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ], pool, profile, release
          ]),
      lengths :=
        (Array.make 4#usize [ 23#usize, 32#usize, 32#usize, 32#usize ]),
      count := 4#usize
    }

theorem request_375 (program pool : Array U8 32#usize) (profile release : Array U8 32#usize) :
 PCG_AddressRef.request_375 program pool profile release = ok (model_375 program pool profile release) := by rfl

theorem domain_375 (program pool : Array U8 32#usize) (profile release : Array U8 32#usize) :
 DescriptorDomain (model_375 program pool profile release) := by
 simp [DescriptorDomain,model_375,Array.make]

#print axioms request_375
#print axioms domain_375

def model_376
(program : Array Std.U8 32#usize) (pool : Array Std.U8 32#usize) :
  Request
  :=
  let a := Array.repeat 32#usize 0#u8
  let a1 := Array.repeat 32#usize 0#u8
  {
      program,
      seeds :=
        (Array.make 4#usize [
          Array.make 32#usize [
            97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 118#u8, 101#u8,
            114#u8, 105#u8, 102#u8, 105#u8, 101#u8, 114#u8, 45#u8, 114#u8,
            101#u8, 103#u8, 105#u8, 115#u8, 116#u8, 114#u8, 121#u8, 45#u8,
            118#u8, 49#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ], pool, a, a1
          ]),
      lengths := (Array.make 4#usize [ 26#usize, 32#usize, 0#usize, 0#usize ]),
      count := 2#usize
    }

theorem request_376 (program pool : Array U8 32#usize) :
 PCG_AddressRef.request_376 program pool = ok (model_376 program pool) := by rfl

theorem domain_376 (program pool : Array U8 32#usize) :
 DescriptorDomain (model_376 program pool) := by
 simp [DescriptorDomain,model_376,Array.make]

#print axioms request_376
#print axioms domain_376

def model_377
(program : Array Std.U8 32#usize) (pool : Array Std.U8 32#usize) :
  Request
  :=
  let a := Array.repeat 32#usize 0#u8
  let a1 := Array.repeat 32#usize 0#u8
  {
      program,
      seeds :=
        (Array.make 4#usize [
          Array.make 32#usize [
            97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 118#u8, 101#u8,
            114#u8, 105#u8, 102#u8, 105#u8, 101#u8, 114#u8, 45#u8, 114#u8,
            101#u8, 103#u8, 105#u8, 115#u8, 116#u8, 114#u8, 121#u8, 45#u8,
            118#u8, 50#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ], pool, a, a1
          ]),
      lengths := (Array.make 4#usize [ 26#usize, 32#usize, 0#usize, 0#usize ]),
      count := 2#usize
    }

theorem request_377 (program pool : Array U8 32#usize) :
 PCG_AddressRef.request_377 program pool = ok (model_377 program pool) := by rfl

theorem domain_377 (program pool : Array U8 32#usize) :
 DescriptorDomain (model_377 program pool) := by
 simp [DescriptorDomain,model_377,Array.make]

#print axioms request_377
#print axioms domain_377

def model_390
(program : Array Std.U8 32#usize) (pool : Array Std.U8 32#usize) :
  Request
  :=
  let a := Array.repeat 32#usize 0#u8
  let a1 := Array.repeat 32#usize 0#u8
  {
      program,
      seeds :=
        (Array.make 4#usize [
          Array.make 32#usize [
            97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 112#u8, 111#u8,
            111#u8, 108#u8, 45#u8, 118#u8, 97#u8, 117#u8, 108#u8, 116#u8,
            45#u8, 97#u8, 117#u8, 116#u8, 104#u8, 111#u8, 114#u8, 105#u8,
            116#u8, 121#u8, 45#u8, 118#u8, 49#u8, 0#u8, 0#u8, 0#u8
            ], pool, a, a1
          ]),
      lengths := (Array.make 4#usize [ 29#usize, 32#usize, 0#usize, 0#usize ]),
      count := 2#usize
    }

theorem request_390 (program pool : Array U8 32#usize) :
 PCG_AddressRef.request_390 program pool = ok (model_390 program pool) := by rfl

theorem domain_390 (program pool : Array U8 32#usize) :
 DescriptorDomain (model_390 program pool) := by
 simp [DescriptorDomain,model_390,Array.make]

#print axioms request_390
#print axioms domain_390

def model_391
(program : Array Std.U8 32#usize) (pool : Array Std.U8 32#usize) :
  Request
  :=
  let a := Array.repeat 32#usize 0#u8
  let a1 := Array.repeat 32#usize 0#u8
  {
      program,
      seeds :=
        (Array.make 4#usize [
          Array.make 32#usize [
            97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 112#u8, 111#u8,
            111#u8, 108#u8, 45#u8, 118#u8, 97#u8, 117#u8, 108#u8, 116#u8,
            45#u8, 116#u8, 111#u8, 107#u8, 101#u8, 110#u8, 45#u8, 118#u8,
            49#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ], pool, a, a1
          ]),
      lengths := (Array.make 4#usize [ 25#usize, 32#usize, 0#usize, 0#usize ]),
      count := 2#usize
    }

theorem request_391 (program pool : Array U8 32#usize) :
 PCG_AddressRef.request_391 program pool = ok (model_391 program pool) := by rfl

theorem domain_391 (program pool : Array U8 32#usize) :
 DescriptorDomain (model_391 program pool) := by
 simp [DescriptorDomain,model_391,Array.make]

#print axioms request_391
#print axioms domain_391

theorem matches (reply : core.result.Result (Array U8 32#usize) PdaError)
 (key : Array U8 32#usize) :
 stored_matches reply key = ok (match reply with
  | .Ok address => decide (address.val = key.val)
  | .Err _ => false) := by
 cases reply <;> simp [stored_matches,NGK_NFV_RequestGuards.array]
#print axioms matches
end PCG_AddressLaws
