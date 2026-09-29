import AspisV8R19.QueryChunkSource
import AspisV8R19.SamplerWordBridge
import Mathlib.Data.List.OfFn

/-! Runtime exact chunks are the eight model words of the actual block.
Prove list partitioning symbolically, not by reducing concrete block bytes. -/
set_option autoImplicit false
namespace AspisV8R19.QueryBlockWords
open Aeneas Aeneas.Std Result QueryChunkExecution QueryChunkModel
open SourceDuplexStep SqueezeOracleBridge SamplerWordRead

theorem four_pos : 0 < (4 : Nat) := by omega
def contents (w : Word) : List U8 := w.val

def blockWords (s : State) : List Word :=
  List.ofFn (fun j : Fin 8 => four (encodeState s) (4*j.val) (by omega))

theorem blockWords_length (s : State) : (blockWords s).length=8 := by
  simp [blockWords]

theorem split_words (ws : List Word) :
    List.toChunksExact 4 four_pos (ws.flatMap contents) = (ws.map contents,[]) := by
  induction ws with
  | nil => rw [List.toChunksExact]; rfl
  | cons word ws ih =>
      have hw : word.val.length=4 := word.property
      have hn : ¬ (word.val++ws.flatMap contents).length < 4 := by
        simp only [List.length_append,hw]; omega
      have ht : (word.val++ws.flatMap contents).take 4=word.val := by
        simpa only [hw] using (List.take_left (l₁:=word.val) (l₂:=ws.flatMap contents))
      have hd : (word.val++ws.flatMap contents).drop 4=ws.flatMap contents := by
        simpa only [hw] using (List.drop_left (l₁:=word.val) (l₂:=ws.flatMap contents))
      rw [List.flatMap_cons,List.toChunksExact]
      change (if _ : (word.val++ws.flatMap contents).length < 4 then _ else _) = _
      simp only [dif_neg hn,show contents word=word.val from rfl,ht,hd,ih,List.map_cons]

theorem flat_block (s : State) :
    (blockWords s).flatMap contents=(encodeState s).val := by
  have hw (j : Fin 8) :
      (four (encodeState s) (4*j.val) (by omega)).val =
        List.ofFn (fun k : Fin 4 => encodeByte (s ⟨4*j.val+k.val,by omega⟩)) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]; exact (four (encodeState s) (4*j.val) (by omega)).property
    · intro i hi hj
      simp only [four,List.getElem_take,List.getElem_drop,encodeState,bytes,
        List.getElem_map,List.getElem_ofFn]
  change ((List.ofFn fun j : Fin 8 => four (encodeState s) (4*j.val) (by omega)).map
    (fun w : Word => w.val)).flatten = _
  rw [List.map_ofFn]
  simp only [Function.comp_def,hw]
  change _=(bytes s).map encodeByte
  simp only [bytes,List.map_ofFn]
  symm
  simpa only [Nat.mul_comm,Fin.cast_eq_self,Function.comp_def] using
    (List.ofFn_mul (m:=8) (n:=4) (fun i => encodeByte (s i)))

def emptySlice : Slice U8 := ⟨[],by simp⟩

theorem chunks_success (s : State) :
    core.slice.Slice.chunks_exact (Array.to_slice (encodeState s)) 4#usize =
      .ok (chunks (blockWords s) emptySlice) := by
  unfold core.slice.Slice.chunks_exact
  simp only [show (4#usize).val=4 from rfl,show 4>0 by decide,dif_pos]
  have hsplit : List.toChunksExact 4 four_pos (Array.to_slice (encodeState s)).val =
      ((blockWords s).map contents,[]) := by
    change List.toChunksExact 4 _ (encodeState s).val = _
    rw [← flat_block,split_words]
  simp only [Array.to_slice] at hsplit ⊢
  simp only [chunks,emptySlice]
  apply congrArg Result.ok
  congr 1
  · apply (List.map_inj_right (f:=fun x : Slice U8 => x.val)
      (fun _ _ h => Subtype.ext h)).1
    simp only [List.map_map,Function.comp_def,Array.to_slice]
    change (List.toChunksExact (4#usize).val _ (encodeState s).val).1.attach.map Subtype.val = _
    rw [List.attach_map_subtype_val]
    exact congrArg Prod.fst hsplit
  · apply Subtype.ext
    exact congrArg Prod.snd hsplit

theorem candidates_exact (s : State) :
    candidates 262143#u32 (blockWords s) = SamplerWords.words 18 s := by
  simp only [candidates,blockWords,List.map_ofFn,SamplerWords.words]
  congr 1
  funext j
  change (_ &&& (262143#u32).bv).toNat = _
  rw [BitVec.toNat_and]
  change (core.num.U32.from_le_bytes (four (encodeState s) (4*j.val) (by omega))).val &&& 262143 = _
  rw [SamplerWordBridge.source_word,SamplerWords.source18_mask]

#print axioms blockWords_length
#print axioms split_words
#print axioms flat_block
#print axioms chunks_success
#print axioms candidates_exact
end AspisV8R19.QueryBlockWords
