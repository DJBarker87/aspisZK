import S6NativeLateHeaderLayoutV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeLateHeaderLayout
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def prepared_header : List U8 :=
  (((((((List.replicate 1520 0#u8).setSlice! 0 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val).
    set 8 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION).set 9 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT).
    setSlice! 10 (core.num.U16.to_le_bytes 32#u16).val).
    setSlice! 12 (core.num.U32.to_le_bytes 800#u32).val).
    setSlice! 16 (core.num.U32.to_le_bytes 688#u32).val).
    setSlice! 20 (core.num.U32.to_le_bytes 1520#u32).val

theorem header_write_eq : prepared_header=header_bytes++List.replicate 1488 0#u8 := by
  exact AspisS6SliceFrame.late_header_writes
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT 0#u8
    (core.num.U16.to_le_bytes 32#u16).val (core.num.U32.to_le_bytes 800#u32).val
    (core.num.U32.to_le_bytes 688#u32).val (core.num.U32.to_le_bytes 1520#u32).val
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.property
    (core.num.U16.to_le_bytes 32#u16).property (core.num.U32.to_le_bytes 800#u32).property
    (core.num.U32.to_le_bytes 688#u32).property (core.num.U32.to_le_bytes 1520#u32).property

theorem assembled (snapshot afterstate : List U8) (hs : snapshot.length=800) (ha : afterstate.length=688) :
    (prepared_header.setSlice! 32 snapshot).setSlice! 832 afterstate=(header_bytes++snapshot)++afterstate := by
  rw [header_write_eq]
  exact AspisS6SliceFrame.late_payload_writes 0#u8 header_bytes snapshot afterstate header_length hs ha

#print axioms header_write_eq
#print axioms assembled
end AspisS6NativeLateHeaderLayout
