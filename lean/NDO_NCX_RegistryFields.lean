import NDO_NCX_ZeroLaws
import JHg_AuditRegistry
set_option autoImplicit false
namespace NCX_RegistryFields
open Aeneas Aeneas.Std Result AspisR1
attribute [local irreducible] JHb_DataRegistry.bytes

theorem read_version : Slice.index_usize JHb_DataRegistry.value 4#usize=ok 3#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataRegistry.length; change 4 < JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.version
#print axioms read_version

theorem read_flags : Slice.index_usize JHb_DataRegistry.value 5#usize=ok 2#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataRegistry.length; change 5 < JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.flags
#print axioms read_flags

theorem read_mode : Slice.index_usize JHb_DataRegistry.value 6#usize=ok 1#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataRegistry.length; change 6 < JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.mode
#print axioms read_mode

theorem read_bump : Slice.index_usize JHb_DataRegistry.value 7#usize=ok 255#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataRegistry.length; change 7 < JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.bump
#print axioms read_bump

def pool : Array U8 32#usize := Array.make 32#usize ([34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8])
theorem read_pool : NCX_Reference.read32 JHb_DataRegistry.value 8#usize=ok pool := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataRegistry.length; change 8+32 ≤ JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.pool
#print axioms read_pool

def authority : Array U8 32#usize := Array.make 32#usize (List.replicate 32 0#u8)
theorem read_authority : NCX_Reference.read32 JHb_DataRegistry.value 40#usize=ok authority := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataRegistry.length; change 40+32 ≤ JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.authority
#print axioms read_authority

def policy : Array U8 32#usize := Array.make 32#usize (List.replicate 32 7#u8)
theorem read_policy : NCX_Reference.read32 JHb_DataRegistry.value 72#usize=ok policy := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataRegistry.length; change 72+32 ≤ JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.policy
#print axioms read_policy

def generation_bytes : Array U8 8#usize := Array.make 8#usize ([1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8])
def generation : U64 := core.num.U64.from_le_bytes generation_bytes
theorem read_generation : NCX_Reference.word JHb_DataRegistry.value 104#usize=ok generation := by
  apply NCX_FieldLaws.word
  · have h:=JHb_DataRegistry.length; change 104+8 ≤ JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.generation
#print axioms read_generation

def delay_bytes : Array U8 8#usize := Array.make 8#usize ([1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8])
def delay : U64 := core.num.U64.from_le_bytes delay_bytes
theorem read_delay : NCX_Reference.word JHb_DataRegistry.value 112#usize=ok delay := by
  apply NCX_FieldLaws.word
  · have h:=JHb_DataRegistry.length; change 112+8 ≤ JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.delay
#print axioms read_delay

def program : Array U8 32#usize := Array.make 32#usize (List.replicate 32 68#u8)
theorem read_program : NCX_Reference.read32 JHb_DataRegistry.value 120#usize=ok program := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataRegistry.length; change 120+32 ≤ JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.program
#print axioms read_program

def loader : Array U8 32#usize := Array.make 32#usize ([2#u8,168#u8,246#u8,145#u8,78#u8,136#u8,161#u8,176#u8,226#u8,16#u8,21#u8,62#u8,247#u8,99#u8,174#u8,43#u8,0#u8,194#u8,185#u8,61#u8,22#u8,193#u8,36#u8,210#u8,192#u8,83#u8,122#u8,16#u8,4#u8,128#u8,0#u8,0#u8])
theorem read_loader : NCX_Reference.read32 JHb_DataRegistry.value 152#usize=ok loader := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataRegistry.length; change 152+32 ≤ JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.loader
#print axioms read_loader

def programdata : Array U8 32#usize := Array.make 32#usize ([10#u8,229#u8,72#u8,238#u8,230#u8,11#u8,166#u8,244#u8,18#u8,189#u8,102#u8,59#u8,14#u8,251#u8,113#u8,3#u8,126#u8,115#u8,18#u8,70#u8,185#u8,8#u8,39#u8,166#u8,11#u8,127#u8,135#u8,77#u8,165#u8,209#u8,161#u8,69#u8])
theorem read_programdata : NCX_Reference.read32 JHb_DataRegistry.value 184#usize=ok programdata := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataRegistry.length; change 184+32 ≤ JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.programdata
#print axioms read_programdata

def executable_hash : Array U8 32#usize := Array.make 32#usize (List.replicate 32 165#u8)
theorem read_executable_hash : NCX_Reference.read32 JHb_DataRegistry.value 216#usize=ok executable_hash := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataRegistry.length; change 216+32 ≤ JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.executable_hash
#print axioms read_executable_hash

theorem read_programdata_bump : Slice.index_usize JHb_DataRegistry.value 248#usize=ok 255#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataRegistry.length; change 248 < JHb_DataRegistry.bytes.length;omega
  · exact JHg_AuditRegistry.programdata_bump
#print axioms read_programdata_bump
end NCX_RegistryFields
