import PCG_AddressRoots
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_CheckpointAddress
open PCG_AddressRef

theorem read8 (b : Array U8 8#usize) (i : Usize) (bound : i.val < 8) :
 Array.index_usize b i = ok (b.val[i.val]'(by have h := b.property; change b.val.length = 8 at h; omega)) := by
 obtain ⟨out,hread,hvalue⟩ := WP.spec_imp_exists
   (Array.index_usize_spec b i (by simpa using bound))
 rw [hread]
 congr 1

def byte (b : Array U8 8#usize) (i : Fin 8) : U8 :=
 b.val[i.val]'(by have h := b.property; change b.val.length = 8 at h; omega)

def padded (sequence : U64) : Array U8 32#usize :=
 let b := core.num.U64.to_le_bytes sequence
 Array.make 32#usize [byte b ⟨0,by decide⟩,byte b ⟨1,by decide⟩,byte b ⟨2,by decide⟩,byte b ⟨3,by decide⟩,byte b ⟨4,by decide⟩,byte b ⟨5,by decide⟩,byte b ⟨6,by decide⟩,byte b ⟨7,by decide⟩,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

theorem le_padded (sequence : U64) : PCG_AddressRef.le_padded sequence = ok (padded sequence) := by
 let b := core.num.U64.to_le_bytes sequence
 have h0 := read8 b 0#usize (by scalar_tac)
 have h1 := read8 b 1#usize (by scalar_tac)
 have h2 := read8 b 2#usize (by scalar_tac)
 have h3 := read8 b 3#usize (by scalar_tac)
 have h4 := read8 b 4#usize (by scalar_tac)
 have h5 := read8 b 5#usize (by scalar_tac)
 have h6 := read8 b 6#usize (by scalar_tac)
 have h7 := read8 b 7#usize (by scalar_tac)
 simp only [PCG_AddressRef.le_padded,lift,pure,bind_tc_ok,h0,h1,h2,h3,h4,h5,h6,h7]
 rfl

def model_323
(program : Array Std.U8 32#usize) (pool : Array Std.U8 32#usize)
  (sequence : Std.U64) :
  Request
  :=
  let a := padded sequence
  let a1 := Array.repeat 32#usize 0#u8
  {
      program,
      seeds :=
        (Array.make 4#usize [
          Array.make 32#usize [
            97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 112#u8, 97#u8,
            105#u8, 114#u8, 45#u8, 102#u8, 111#u8, 114#u8, 101#u8, 115#u8,
            116#u8, 45#u8, 99#u8, 104#u8, 101#u8, 99#u8, 107#u8, 112#u8,
            111#u8, 105#u8, 110#u8, 116#u8, 45#u8, 118#u8, 49#u8, 0#u8
            ], pool, a, a1
          ]),
      lengths := (Array.make 4#usize [ 31#usize, 32#usize, 8#usize, 0#usize ]),
      count := 3#usize
    }

theorem request_323 (program pool : Array U8 32#usize) (sequence : U64) :
 PCG_AddressRef.request_323 program pool sequence = ok (model_323 program pool sequence) := by
 simp only [PCG_AddressRef.request_323,le_padded,bind_tc_ok]
 rfl

theorem domain_323 (program pool : Array U8 32#usize) (sequence : U64) :
 PCG_AddressLaws.DescriptorDomain (model_323 program pool sequence) := by
 simp [PCG_AddressLaws.DescriptorDomain,model_323,Array.make]

theorem row_323 (program pool : Array U8 32#usize) (sequence : U64)
 (op38 : PCG_AddressRoots.Op38) :
 PCG_AddressRoots.nativeFind (PCG_AddressRef.request_323 program pool sequence) op38 =
   ok ⟨[PCG_RequestCarrier.request (model_323 program pool sequence)],
    PCG_SdkPda.findReply (op38 (PCG_RequestCarrier.request (model_323 program pool sequence)))⟩ ∧
 PCG_SdkPda.Domain (PCG_RequestCarrier.request (model_323 program pool sequence)) ∧
 (PCG_RequestCarrier.request (model_323 program pool sequence)).program = program ∧
 (PCG_RequestCarrier.request (model_323 program pool sequence)).seeds.val.length = 3 := by
 constructor
 · rw [request_323]
   rfl
 · refine ⟨PCG_RequestCarrier.sdk_domain _,rfl,?_⟩
   rw [PCG_RequestCarrier.exact_count _ (domain_323 program pool sequence).1]
   rfl

#print axioms read8
#print axioms le_padded
#print axioms request_323
#print axioms domain_323
#print axioms row_323
end PCG_CheckpointAddress
