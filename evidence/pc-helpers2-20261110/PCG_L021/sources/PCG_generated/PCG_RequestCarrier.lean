import PCG_AddressLaws
import PCG_SdkPda
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_RequestCarrier
open PCG_AddressRef

def seed (bytes : Array U8 32#usize) (length : Usize) : Slice U8 :=
 ⟨bytes.val.take length.val, by
   have h : bytes.val.length = 32 := by simpa using bytes.property
   have hm : 32 ≤ Usize.max := by scalar_tac
   simp only [List.length_take]
   omega⟩

theorem seed_bound (bytes : Array U8 32#usize) (length : Usize) :
 (seed bytes length).val.length ≤ 32 := by
 have h : bytes.val.length = 32 := by simpa using bytes.property
 simp only [seed,List.length_take]
 omega

def windows (q : Request) : List (Slice U8) :=
 ((q.seeds.val.zip q.lengths.val).take q.count.val).map (fun p => seed p.1 p.2)

theorem windows_bound (q : Request) : (windows q).length ≤ 4 := by
 have h : q.seeds.val.length = 4 := by simpa using q.seeds.property
 simp only [windows,List.length_map,List.length_take,List.length_zip]
 omega

def request (q : Request) : PCG_SdkPda.Request :=
 {seeds := ⟨windows q, by
   have h := windows_bound q
   have hm : 4 ≤ Usize.max := by scalar_tac
   omega⟩, program := q.program}

/-- No descriptor is dropped on the exact request domain proved for each helper. -/
theorem exact_count (q : Request) (h : q.count.val ≤ 4) :
 (request q).seeds.val.length = q.count.val := by
 have hs : q.seeds.val.length = 4 := by simpa using q.seeds.property
 have hl : q.lengths.val.length = 4 := by simpa using q.lengths.property
 simp only [request,windows,List.length_map,List.length_take,List.length_zip]
 omega

/-- SDK admission is discharged by the request's fixed carriers and count. -/
theorem sdk_domain (q : Request) : PCG_SdkPda.Domain (request q) := by
 constructor
 · have h := windows_bound q
   change (windows q).length ≤ 16
   omega
 · intro s member
   change s ∈ windows q at member
   obtain ⟨p,_,rfl⟩ := List.mem_map.mp member
   exact seed_bound p.1 p.2

theorem same_program (q : Request) : (request q).program = q.program := rfl
#print axioms seed_bound
#print axioms windows_bound
#print axioms exact_count
#print axioms sdk_domain
#print axioms same_program
end PCG_RequestCarrier
