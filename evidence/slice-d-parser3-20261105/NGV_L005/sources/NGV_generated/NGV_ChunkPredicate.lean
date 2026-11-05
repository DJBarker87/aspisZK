import NGV_ChunkWords
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ChunkPredicate
open NGO_PrefixLimbsLaw NFU_Retarget
 theorem word (bs : Slice U8) (size : bs.val.length=32) (j : Fin 8) :
 (atWord (NGV_ChunkWords.words bs size) j).val=
 LPl_Kit_Bytes.le32 ((bs.val.drop (4*j.val)).take 4) := by
 simp only [atWord,NGV_ChunkWords.words,Array.make,List.getElem_map,List.getElem_finRange]
 exact (NGO_ValidatorWindows.word bs.val (4*j.val) (by omega)).symm
 theorem valid (bs : Slice U8) (size : bs.val.length=32) :
 LPl_Kit_Bytes.validChunk 8 true bs.val=true ↔
 (∀ j : Fin 8, (atWord (NGV_ChunkWords.words bs size) j).val<2147483647) ∧
 (atWord (NGV_ChunkWords.words bs size) 4).val=0 ∧
 (atWord (NGV_ChunkWords.words bs size) 5).val=0 ∧
 (atWord (NGV_ChunkWords.words bs size) 6).val=0 ∧
 (atWord (NGV_ChunkWords.words bs size) 7).val=0 := by
 simp only [LPl_Kit_Bytes.validChunk,List.all_eq_true,List.mem_range,
   Bool.and_eq_true,Bool.or_eq_true,Bool.not_true,Bool.false_eq_true,false_or,decide_eq_true_eq]
 constructor
 · intro h
   refine ⟨?_,?_,?_,?_,?_⟩
   · intro j;rw [word];exact (h j.val j.isLt).1
   all_goals rw [word];first | exact (h 4 (by omega)).2.resolve_left (by omega) | exact (h 5 (by omega)).2.resolve_left (by omega) | exact (h 6 (by omega)).2.resolve_left (by omega) | exact (h 7 (by omega)).2.resolve_left (by omega)
 · rintro ⟨canonical,h4,h5,h6,h7⟩ j bound
   have canon := canonical ⟨j,bound⟩
   rw [word] at canon
   refine ⟨canon,?_⟩
   by_cases low : j<4
   · exact Or.inl low
   · right
     interval_cases j <;> simpa only [word] using (by assumption : (atWord (NGV_ChunkWords.words bs size) _).val=0)
#print axioms word
#print axioms valid
end NGV_ChunkPredicate
