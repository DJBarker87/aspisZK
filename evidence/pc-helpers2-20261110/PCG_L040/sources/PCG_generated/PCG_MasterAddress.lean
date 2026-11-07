import PCG_MasterRef.Funs
import PCG_AddressRoots
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_MasterAddress
open AdapterRw
abbrev Key := Array U8 32#usize
abbrev Master := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1

def model
(program : Array Std.U8 32#usize) (mint : Array Std.U8 32#usize)
  (bump : Std.U8) :
  PCG_MasterRef.Request
  :=
  let a := Array.repeat 32#usize 0#u8
  {
      program,
      seeds :=
        (Array.make 4#usize [
          Array.make 32#usize [
            97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 112#u8, 97#u8,
            105#u8, 114#u8, 45#u8, 102#u8, 111#u8, 114#u8, 101#u8, 115#u8,
            116#u8, 45#u8, 109#u8, 97#u8, 115#u8, 116#u8, 101#u8, 114#u8,
            45#u8, 118#u8, 49#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ], mint,
          Array.make 32#usize [
            bump, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
            0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
            0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ], a
          ]),
      lengths := (Array.make 4#usize [ 27#usize, 32#usize, 1#usize, 0#usize ]),
      count := 3#usize
    }

def toAddress (q : PCG_MasterRef.Request) : PCG_AddressRef.Request :=
 {program:=q.program,seeds:=q.seeds,lengths:=q.lengths,count:=q.count}

theorem request (program mint : Key) (bump : U8) :
 PCG_MasterRef.request_318 program mint bump = ok (model program mint bump) := rfl

def q (program : Key) (master : Master) : PCG_SdkPda.Request :=
 PCG_RequestCarrier.request (toAddress (model program master.identity.asset_mint master.bump))

def native (program : Key) (master : Master) (key : Key) (op38 : PCG_AddressRoots.Op38) := do
 let request ← PCG_MasterRef.request_318 program master.identity.asset_mint master.bump
 ok (PCG_AddressRoots.nativeStored (PCG_RequestCarrier.request (toAddress request)) key op38)

/-- The child is the CLOSED/gated-candidate379 packet, at the SAME program,
master mint, persisted bump and candidate key. No child result is a premise. -/
theorem row_318 (program : Key) (master : Master) (key : Key) (op38 : PCG_AddressRoots.Op38) :
 native program master key op38 = ok ⟨[q program master],do
   let reply ← PCG_SdkPda.createReply (op38 (q program master))
   ok (match reply with
    | .Ok address => decide (address.val = key.val)
    | .Err _ => false)⟩ ∧
 PCG_SdkPda.Domain (q program master) ∧
 (q program master).program = program ∧ (q program master).seeds.val.length = 3 := by
 have domain : PCG_SdkPda.Domain (q program master) := PCG_RequestCarrier.sdk_domain _
 constructor
 · simp only [native,request,bind_tc_ok]
   exact congrArg Result.ok (PCG_AddressRoots.row_379 _ key op38 domain)
 · refine ⟨domain,rfl,?_⟩
   rw [PCG_RequestCarrier.exact_count _ (by simp [toAddress,model])]
   rfl

#print axioms request
#print axioms row_318
end PCG_MasterAddress
