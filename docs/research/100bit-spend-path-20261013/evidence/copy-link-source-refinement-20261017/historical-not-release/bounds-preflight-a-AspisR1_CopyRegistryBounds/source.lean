import AspisR1.CopyLinkLoopCandidate
import CopyLinkWeightExact

/-! Only literal integer descriptor bounds are checked here. No finite-field
arithmetic, recurrence, registry fold or generated certificate is normalized. -/
set_option autoImplicit false
namespace AspisR1.CopyRegistryBounds
open Aeneas Aeneas.Std
open AspisR1.CopyLinkWeightExact
abbrev registry := AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_LINKS

def DescriptorValid (link : Raw) : Prop :=
  link.tag.val < 2147483647 ∧ link.weight_kind.val < 5 ∧ link.weight_level.val < 64 ∧
  link.producer.row.val < 1024 ∧ link.producer.slot.val < 2 ∧ link.producer.pattern.val < 14 ∧
  link.consumer.row.val < 1024 ∧ link.consumer.slot.val < 2 ∧ link.consumer.pattern.val < 14

instance (link : Raw) : Decidable (DescriptorValid link) :=
  inferInstanceAs (Decidable (link.tag.val < 2147483647 ∧ link.weight_kind.val < 5 ∧ link.weight_level.val < 64 ∧
    link.producer.row.val < 1024 ∧ link.producer.slot.val < 2 ∧ link.producer.pattern.val < 14 ∧
    link.consumer.row.val < 1024 ∧ link.consumer.slot.val < 2 ∧ link.consumer.pattern.val < 14))

private def chunk_0 : List Raw := [
    {
      tag := 1124073472#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 27#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 32#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1124073473#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 43#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 48#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1124073474#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 411#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 416#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1124073475#u32,
      weight_kind := 1#u8,
      weight_level := 0#u8,
      producer := { row := 443#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 448#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1124073476#u32,
      weight_kind := 1#u8,
      weight_level := 0#u8,
      producer := { row := 459#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 464#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1124073477#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 491#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 496#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1124073478#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 507#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 512#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1124073479#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 11#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 28#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1124073480#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 12#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 412#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1124073481#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 44#u16, slot := 0#u8, pattern := 2#u8 },
      consumer := { row := 428#u16, slot := 0#u8, pattern := 3#u8 }
    },
    {
      tag := 1124073482#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 60#u16, slot := 0#u8, pattern := 4#u8 },
      consumer := { row := 428#u16, slot := 1#u8, pattern := 5#u8 }
    },
    {
      tag := 1124073483#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 44#u16, slot := 1#u8, pattern := 6#u8 },
      consumer := { row := 1008#u16, slot := 0#u8, pattern := 7#u8 }
    },
    {
      tag := 1124073484#u32,
      weight_kind := 1#u8,
      weight_level := 0#u8,
      producer := { row := 460#u16, slot := 0#u8, pattern := 6#u8 },
      consumer := { row := 1010#u16, slot := 0#u8, pattern := 7#u8 }
    },
    {
      tag := 1124073485#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 508#u16, slot := 0#u8, pattern := 6#u8 },
      consumer := { row := 1012#u16, slot := 0#u8, pattern := 7#u8 }
    },
    {
      tag := 1124073486#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1008#u16, slot := 0#u8, pattern := 7#u8 },
      consumer := { row := 1014#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1124073487#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1010#u16, slot := 0#u8, pattern := 7#u8 },
      consumer := { row := 1014#u16, slot := 1#u8, pattern := 8#u8 }
    }
  ]

theorem first_chunk_valid : List.Forall DescriptorValid chunk_0 := by
  decide

#print axioms first_chunk_valid
end AspisR1.CopyRegistryBounds
