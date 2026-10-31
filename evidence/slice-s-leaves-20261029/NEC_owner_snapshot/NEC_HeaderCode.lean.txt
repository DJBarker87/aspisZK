import NEC_LiveHeaderRef.Funs
set_option autoImplicit false
namespace NEC_HeaderCode
open Aeneas Aeneas.Std Result

def read (a : Array U8 48#usize) (i : Fin 48) : U8 :=
 a.val[i.val]'(by simpa [a.property] using i.isLt)

theorem index_read (a : Array U8 48#usize) (i : Fin 48) :
 Array.index_usize a (Usize.ofNatCore i.val (by scalar_tac))=ok (read a i) := by
 have hidx : i.val<a.val.length := by simpa [a.property] using i.isLt
 unfold Array.index_usize
 change (match a.val[i.val]? with
  | none=>Result.fail Error.arrayOutOfBounds
  | some x=>ok x)=ok (read a i)
 rw [List.getElem?_eq_getElem hidx]
 rfl

def code (length : Usize) (bytes : Array U8 48#usize) : U8 :=
 if length != 800#usize then 1#u8 else
 if read bytes ⟨0,by decide⟩ != 65#u8 then 2#u8 else
 if read bytes ⟨1,by decide⟩ != 83#u8 then 2#u8 else
 if read bytes ⟨2,by decide⟩ != 80#u8 then 2#u8 else
 if read bytes ⟨3,by decide⟩ != 76#u8 then 2#u8 else
 if read bytes ⟨4,by decide⟩ != 73#u8 then 2#u8 else
 if read bytes ⟨5,by decide⟩ != 86#u8 then 2#u8 else
 if read bytes ⟨6,by decide⟩ != 69#u8 then 2#u8 else
 if read bytes ⟨7,by decide⟩ != 49#u8 then 2#u8 else
 if read bytes ⟨8,by decide⟩ != 1#u8 then 3#u8 else
 if read bytes ⟨9,by decide⟩ != 0#u8 then 4#u8 else
 if read bytes ⟨10,by decide⟩ != 0#u8 then 4#u8 else
 if read bytes ⟨11,by decide⟩ != 0#u8 then 4#u8 else
 if read bytes ⟨12,by decide⟩ != 0#u8 then 4#u8 else
 if read bytes ⟨13,by decide⟩ != 0#u8 then 4#u8 else
 if read bytes ⟨14,by decide⟩ != 0#u8 then 4#u8 else
 if read bytes ⟨15,by decide⟩ != 0#u8 then 4#u8 else
 if read bytes ⟨16,by decide⟩ != 65#u8 then 5#u8 else
 if read bytes ⟨17,by decide⟩ != 83#u8 then 5#u8 else
 if read bytes ⟨18,by decide⟩ != 80#u8 then 5#u8 else
 if read bytes ⟨19,by decide⟩ != 80#u8 then 5#u8 else
 if read bytes ⟨20,by decide⟩ != 65#u8 then 5#u8 else
 if read bytes ⟨21,by decide⟩ != 73#u8 then 5#u8 else
 if read bytes ⟨22,by decide⟩ != 82#u8 then 5#u8 else
 if read bytes ⟨23,by decide⟩ != 49#u8 then 5#u8 else
 if read bytes ⟨24,by decide⟩ != 1#u8 then 5#u8 else
 if read bytes ⟨25,by decide⟩ != 20#u8 then 5#u8 else
 if read bytes ⟨26,by decide⟩ != 21#u8 then 5#u8 else
 if read bytes ⟨27,by decide⟩ != 7#u8 then 5#u8 else
 if read bytes ⟨28,by decide⟩ != 1#u8 then 5#u8 else
 if read bytes ⟨29,by decide⟩ != 1#u8 then 5#u8 else
 if read bytes ⟨30,by decide⟩ != 1#u8 then 5#u8 else
 if read bytes ⟨31,by decide⟩ != 1#u8 then 5#u8 else
 if read bytes ⟨32,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨33,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨34,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨35,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨36,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨37,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨38,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨39,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨40,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨41,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨42,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨43,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨44,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨45,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨46,by decide⟩ != 0#u8 then 5#u8 else
 if read bytes ⟨47,by decide⟩ != 0#u8 then 5#u8 else
 0#u8

theorem emitted (length : Usize) (bytes : Array U8 48#usize) :
 NEC_LiveHeaderRef.live_header_ref length bytes=ok (code length bytes) := by
 have i0 : Array.index_usize bytes 0#usize=ok (read bytes ⟨0,by decide⟩) := index_read bytes ⟨0,by decide⟩
 have i1 : Array.index_usize bytes 1#usize=ok (read bytes ⟨1,by decide⟩) := index_read bytes ⟨1,by decide⟩
 have i2 : Array.index_usize bytes 2#usize=ok (read bytes ⟨2,by decide⟩) := index_read bytes ⟨2,by decide⟩
 have i3 : Array.index_usize bytes 3#usize=ok (read bytes ⟨3,by decide⟩) := index_read bytes ⟨3,by decide⟩
 have i4 : Array.index_usize bytes 4#usize=ok (read bytes ⟨4,by decide⟩) := index_read bytes ⟨4,by decide⟩
 have i5 : Array.index_usize bytes 5#usize=ok (read bytes ⟨5,by decide⟩) := index_read bytes ⟨5,by decide⟩
 have i6 : Array.index_usize bytes 6#usize=ok (read bytes ⟨6,by decide⟩) := index_read bytes ⟨6,by decide⟩
 have i7 : Array.index_usize bytes 7#usize=ok (read bytes ⟨7,by decide⟩) := index_read bytes ⟨7,by decide⟩
 have i8 : Array.index_usize bytes 8#usize=ok (read bytes ⟨8,by decide⟩) := index_read bytes ⟨8,by decide⟩
 have i9 : Array.index_usize bytes 9#usize=ok (read bytes ⟨9,by decide⟩) := index_read bytes ⟨9,by decide⟩
 have i10 : Array.index_usize bytes 10#usize=ok (read bytes ⟨10,by decide⟩) := index_read bytes ⟨10,by decide⟩
 have i11 : Array.index_usize bytes 11#usize=ok (read bytes ⟨11,by decide⟩) := index_read bytes ⟨11,by decide⟩
 have i12 : Array.index_usize bytes 12#usize=ok (read bytes ⟨12,by decide⟩) := index_read bytes ⟨12,by decide⟩
 have i13 : Array.index_usize bytes 13#usize=ok (read bytes ⟨13,by decide⟩) := index_read bytes ⟨13,by decide⟩
 have i14 : Array.index_usize bytes 14#usize=ok (read bytes ⟨14,by decide⟩) := index_read bytes ⟨14,by decide⟩
 have i15 : Array.index_usize bytes 15#usize=ok (read bytes ⟨15,by decide⟩) := index_read bytes ⟨15,by decide⟩
 have i16 : Array.index_usize bytes 16#usize=ok (read bytes ⟨16,by decide⟩) := index_read bytes ⟨16,by decide⟩
 have i17 : Array.index_usize bytes 17#usize=ok (read bytes ⟨17,by decide⟩) := index_read bytes ⟨17,by decide⟩
 have i18 : Array.index_usize bytes 18#usize=ok (read bytes ⟨18,by decide⟩) := index_read bytes ⟨18,by decide⟩
 have i19 : Array.index_usize bytes 19#usize=ok (read bytes ⟨19,by decide⟩) := index_read bytes ⟨19,by decide⟩
 have i20 : Array.index_usize bytes 20#usize=ok (read bytes ⟨20,by decide⟩) := index_read bytes ⟨20,by decide⟩
 have i21 : Array.index_usize bytes 21#usize=ok (read bytes ⟨21,by decide⟩) := index_read bytes ⟨21,by decide⟩
 have i22 : Array.index_usize bytes 22#usize=ok (read bytes ⟨22,by decide⟩) := index_read bytes ⟨22,by decide⟩
 have i23 : Array.index_usize bytes 23#usize=ok (read bytes ⟨23,by decide⟩) := index_read bytes ⟨23,by decide⟩
 have i24 : Array.index_usize bytes 24#usize=ok (read bytes ⟨24,by decide⟩) := index_read bytes ⟨24,by decide⟩
 have i25 : Array.index_usize bytes 25#usize=ok (read bytes ⟨25,by decide⟩) := index_read bytes ⟨25,by decide⟩
 have i26 : Array.index_usize bytes 26#usize=ok (read bytes ⟨26,by decide⟩) := index_read bytes ⟨26,by decide⟩
 have i27 : Array.index_usize bytes 27#usize=ok (read bytes ⟨27,by decide⟩) := index_read bytes ⟨27,by decide⟩
 have i28 : Array.index_usize bytes 28#usize=ok (read bytes ⟨28,by decide⟩) := index_read bytes ⟨28,by decide⟩
 have i29 : Array.index_usize bytes 29#usize=ok (read bytes ⟨29,by decide⟩) := index_read bytes ⟨29,by decide⟩
 have i30 : Array.index_usize bytes 30#usize=ok (read bytes ⟨30,by decide⟩) := index_read bytes ⟨30,by decide⟩
 have i31 : Array.index_usize bytes 31#usize=ok (read bytes ⟨31,by decide⟩) := index_read bytes ⟨31,by decide⟩
 have i32 : Array.index_usize bytes 32#usize=ok (read bytes ⟨32,by decide⟩) := index_read bytes ⟨32,by decide⟩
 have i33 : Array.index_usize bytes 33#usize=ok (read bytes ⟨33,by decide⟩) := index_read bytes ⟨33,by decide⟩
 have i34 : Array.index_usize bytes 34#usize=ok (read bytes ⟨34,by decide⟩) := index_read bytes ⟨34,by decide⟩
 have i35 : Array.index_usize bytes 35#usize=ok (read bytes ⟨35,by decide⟩) := index_read bytes ⟨35,by decide⟩
 have i36 : Array.index_usize bytes 36#usize=ok (read bytes ⟨36,by decide⟩) := index_read bytes ⟨36,by decide⟩
 have i37 : Array.index_usize bytes 37#usize=ok (read bytes ⟨37,by decide⟩) := index_read bytes ⟨37,by decide⟩
 have i38 : Array.index_usize bytes 38#usize=ok (read bytes ⟨38,by decide⟩) := index_read bytes ⟨38,by decide⟩
 have i39 : Array.index_usize bytes 39#usize=ok (read bytes ⟨39,by decide⟩) := index_read bytes ⟨39,by decide⟩
 have i40 : Array.index_usize bytes 40#usize=ok (read bytes ⟨40,by decide⟩) := index_read bytes ⟨40,by decide⟩
 have i41 : Array.index_usize bytes 41#usize=ok (read bytes ⟨41,by decide⟩) := index_read bytes ⟨41,by decide⟩
 have i42 : Array.index_usize bytes 42#usize=ok (read bytes ⟨42,by decide⟩) := index_read bytes ⟨42,by decide⟩
 have i43 : Array.index_usize bytes 43#usize=ok (read bytes ⟨43,by decide⟩) := index_read bytes ⟨43,by decide⟩
 have i44 : Array.index_usize bytes 44#usize=ok (read bytes ⟨44,by decide⟩) := index_read bytes ⟨44,by decide⟩
 have i45 : Array.index_usize bytes 45#usize=ok (read bytes ⟨45,by decide⟩) := index_read bytes ⟨45,by decide⟩
 have i46 : Array.index_usize bytes 46#usize=ok (read bytes ⟨46,by decide⟩) := index_read bytes ⟨46,by decide⟩
 have i47 : Array.index_usize bytes 47#usize=ok (read bytes ⟨47,by decide⟩) := index_read bytes ⟨47,by decide⟩
 simp only [NEC_LiveHeaderRef.live_header_ref,NEC_LiveHeaderRef.magic_ok,NEC_LiveHeaderRef.binding0_ok,NEC_LiveHeaderRef.binding1_ok,NEC_LiveHeaderRef.binding2_ok,NEC_LiveHeaderRef.binding3_ok,code,i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,i29,i30,i31,i32,i33,i34,i35,i36,i37,i38,i39,i40,i41,i42,i43,i44,i45,i46,i47,bind_tc_ok]
 all_goals repeat' first | split | rfl

#print axioms index_read
#print axioms emitted
end NEC_HeaderCode
