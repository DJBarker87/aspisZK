import R1Z.PDict_FormatterStorePath
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FormatterIOMap
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap

theorem io14 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.fs.File.open (types b F) (selected b F ops) = @std.fs.File.open b ops := rfl
#print axioms io14

theorem io15 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.fs.File.sync_all (types b F) (selected b F ops) = @std.fs.File.sync_all b ops := rfl
#print axioms io15

theorem io19 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.fs.OpenOptions.new (types b F) (selected b F ops) = @std.fs.OpenOptions.new b ops := rfl
#print axioms io19

theorem io20 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.fs.OpenOptions.write (types b F) (selected b F ops) = @std.fs.OpenOptions.write b ops := rfl
#print axioms io20

theorem io21 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.fs.OpenOptions.create_new (types b F) (selected b F ops) = @std.fs.OpenOptions.create_new b ops := rfl
#print axioms io21

theorem io22 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.fs.OpenOptions.open (types b F) (selected b F ops) = @std.fs.OpenOptions.open b ops := rfl
#print axioms io22

theorem io23 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.io.error.Error.kind (types b F) (selected b F ops) = @std.io.error.Error.kind b ops := rfl
#print axioms io23

theorem io24 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode (types b F) (selected b F ops) = @std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode b ops := rfl
#print axioms io24

theorem io25 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref (types b F) (selected b F ops) = @std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref b ops := rfl
#print axioms io25

theorem io26 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.path.Path.join (types b F) (selected b F ops) = @std.path.Path.join b ops := rfl
#print axioms io26

theorem io27 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.path.Path.Insts.CoreConvertAsRefPath.as_ref (types b F) (selected b F ops) = @std.path.Path.Insts.CoreConvertAsRefPath.as_ref b ops := rfl
#print axioms io27

theorem io28 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @alloc.string.String.Insts.CoreConvertAsRefPath.as_ref (types b F) (selected b F ops) = @alloc.string.String.Insts.CoreConvertAsRefPath.as_ref b ops := rfl
#print axioms io28

theorem io29 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref (types b F) (selected b F ops) = @std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref b ops := rfl
#print axioms io29

theorem io30 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @alloc.string.String.with_capacity (types b F) (selected b F ops) = @alloc.string.String.with_capacity b ops := rfl
#print axioms io30

theorem io31 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @alloc.string.String.push_str (types b F) (selected b F ops) = @alloc.string.String.push_str b ops := rfl
#print axioms io31

theorem io261 (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @std.fs.File.Insts.StdIoWrite.write_all (types b F) (selected b F ops) = @std.fs.File.Insts.StdIoWrite.write_all b ops := rfl
#print axioms io261

theorem sync_directory (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @aspis_prover.state_only_entropy.sync_directory (types b F) (selected b F ops) =
    @aspis_prover.state_only_entropy.sync_directory b ops := by
  delta aspis_prover.state_only_entropy.sync_directory
  delta aspis_prover.state_only_entropy.sync_directory.match_1
  rfl
#print axioms sync_directory
end R1Z.PDict_FormatterIOMap
