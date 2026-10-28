import R1Z.PV_DL_UpdateViews
import R1Z.PV_DL_UpdateCopy
import R1Z.PV_DL_StorageIdentity
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_UpdateCarrier
open PV_CBL_LibraryShapes PV_CBL_GenericArrayPower
set_option autoImplicit false
abbrev Blocks (N : Type) := Slice (GenericArray U8 N (Storage U8 6))

def blockList (N : Type) (bytes : List U8) : List (GenericArray U8 N (Storage U8 6)) :=
  (PV_DL_UpdateViews.views (bytes.length/64) bytes).map
    (fun block => ⟨PV_DL_StorageBuild.build 6 (fun i => block[i]!)⟩)

theorem block_decoding (N : Type) (blocks : List (List U8))
    (h : ∀ block∈blocks,block.length=64) :
    (blocks.map (fun block => (⟨PV_DL_StorageBuild.build 6 (fun i => block[i]!)⟩ :
      GenericArray U8 N (Storage U8 6)))).flatMap (fun block => flatten 6 block.data)=
      blocks.flatMap id := by
  revert h
  induction blocks with
  | nil => intro h;rfl
  | cons block tail ih =>
    intro h
    simp only [List.map_cons,List.flatMap_cons]
    rw [PV_DL_StorageBuild.reconstruct 6 block (h block (by simp only [List.mem_cons_self]))]
    rw [ih (fun b hb => h b (by simp only [List.mem_cons];exact Or.inr hb))]
    rfl

theorem decoded_blocks (N : Type) (bytes : List U8) :
    (blockList N bytes).flatMap (fun block => flatten 6 block.data)=(PV_DL_BatchPlan.bulk bytes).1 := by
  unfold blockList
  rw [block_decoding N _ (fun b hb => PV_DL_UpdateViews.native_block_lengths bytes b hb)]
  exact PV_DL_UpdateViews.native_bulk bytes

def compress {T N : Type} (update : T → Blocks N → Result T)
    (state : T) (bytes : List U8) : Result T :=
  if h : (blockList N bytes).length ≤ Usize.max then update state ⟨blockList N bytes,h⟩ else fail .panic

theorem block_count (N : Type) (bytes : List U8) :
    (blockList N bytes).length=bytes.length/64 := by
  simp only [blockList,List.length_map,PV_DL_UpdateViews.count]

theorem compression_call {T N : Type} (update : T → Blocks N → Result T)
    (state : T) (bytes : List U8) (bound : bytes.length ≤ Usize.max) :
    compress update state bytes=update state
      ⟨blockList N bytes,by rw [block_count];exact le_trans (Nat.div_le_self _ _) bound⟩ := by
  unfold compress
  rw [dif_pos (by rw [block_count];exact le_trans (Nat.div_le_self _ _) bound)]

theorem native_batch_bound (buffer input : List U8) (pos : Nat)
    (hb : buffer.length=64) (hp : pos<64) (hi : input.length ≤ Usize.max)
    (batch : List U8) (h : batch∈(PV_DL_UpdatePlan.value buffer pos input).batches) :
    batch.length ≤ Usize.max := by
  by_cases hn : input.length<64-pos
  · simp only [PV_DL_UpdatePlan.value,if_pos hn,List.not_mem_nil] at h
  · simp only [PV_DL_UpdatePlan.value,if_neg hn,List.mem_append] at h
    rcases h with first|bulk
    · by_cases hz : pos=0
      · simp only [hz,if_true,List.not_mem_nil] at first
      · simp only [hz,if_false,List.mem_singleton] at first
        subst batch
        rw [PV_DL_UpdatePlan.first_length buffer input pos hb hp (by omega)]
        scalar_tac
    · unfold PV_DL_BatchPlan.events at bulk
      split at bulk
      · simp only [List.not_mem_nil] at bulk
      · simp only [List.mem_singleton] at bulk
        subst batch
        simp only [PV_DL_BatchPlan.bulk,List.length_take,List.length_drop]
        omega

def encode {T : Type} (result : T × List U8 × Nat) : Result (Wrapper T (Storage U8 6)) :=
  if h : result.2.2<256 then
    ok ⟨result.1,⟨PV_DL_StorageBuild.build 6 (fun i => result.2.1[i]!),
      U8.ofNatCore result.2.2 h,()⟩⟩
  else fail .panic

def callback {T N : Type} (update : T → Blocks N → Result T)
    (self : Wrapper T (Storage U8 6)) (input : Slice U8) : Result (Wrapper T (Storage U8 6)) := do
  let result ← PV_DL_UpdatePlan.run (compress update) self.core
    (flatten 6 self.buffer.buffer) self.buffer.pos.val input.val
  encode result

def value {T N : Type} (update : T → Blocks N → Result T)
    (self : Wrapper T (Storage U8 6)) (input : Slice U8) : Result (Wrapper T (Storage U8 6)) := do
  let result ← PV_DL_UpdatePlan.model (compress update) self.core
    (flatten 6 self.buffer.buffer) self.buffer.pos.val input.val
  encode result

theorem complete {T N : Type} (update : T → Blocks N → Result T)
    (self : Wrapper T (Storage U8 6)) (input : Slice U8) :
    callback update self input=value update self input := by
  unfold callback value
  rw [PV_DL_UpdatePlan.complete]

theorem encoding_valid {T : Type} (state : T) (buffer : List U8) (pos : Nat)
    (hb : buffer.length=64) (hp : pos<64) :
    encode (state,buffer,pos)=ok ⟨state,⟨PV_DL_StorageBuild.build 6 (fun i => buffer[i]!),
      U8.ofNatCore pos (by simp only [UScalarTy.U8_numBits_eq];omega),()⟩⟩ := by
  unfold encode
  dsimp only
  rw [dif_pos (by omega)]

theorem decoded {T : Type} (state : T) (buffer : List U8) (pos : Nat)
    (hb : buffer.length=64) (hp : pos<64) :
    flatten 6 (PV_DL_StorageBuild.build 6 (fun i => buffer[i]!))=buffer :=
  PV_DL_StorageBuild.reconstruct 6 buffer hb

#print axioms blockList
#print axioms block_decoding
#print axioms decoded_blocks
#print axioms compress
#print axioms block_count
#print axioms compression_call
#print axioms native_batch_bound
#print axioms encode
#print axioms callback
#print axioms value
#print axioms complete
#print axioms encoding_valid
#print axioms decoded
end R1Z.PV_DL_UpdateCarrier
