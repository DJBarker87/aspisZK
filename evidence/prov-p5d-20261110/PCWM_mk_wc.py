import re,glob
def blk(F,name):
    t=open(F).read()
    m=re.search(r'(/--[^\n]*\n(?:    [^\n]*\n)*)((?:@\[[^\n]*\]\n)?def '+re.escape(name)+r'\b[^\n]*\n(?:  [^\n]*\n)*)',t)
    return m.group(1)+m.group(2)+'\n'
E3=glob.glob('../prov-p1e-20261109/PCQF_E003_emitted/raw/*/Funs.lean')[0]
E10=glob.glob('../prov-p1e-20261109/PCQF_E010_emitted/raw/*/Funs.lean')[0]
E4=glob.glob('../prov-p1e-20261109/PCQF_E004_emitted/raw/*/Funs.lean')[0]
E1=glob.glob('PCWM_E001_emitted/raw/*/Funs.lean')[0]
fresh=blk(E3,'spend.VALUE_LIMIT')+blk(E10,'pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION')+blk(E10,'pool_v1.format.POOL_V1_TREE_DEPTH')+blk(E4,'pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY')+blk(E1,'field.M31.to_le_bytes')
G='AspisR1WithdrawalCaller'
hdr=f'''-- PCWM_ w1: fresh frozen-4bb3b3f (overflow checks ON) definitions of the five WithdrawalCaller.Funs items that are not loops, against the gate constants.
-- fresh sources: spend.VALUE_LIMIT <- PCQF_E003; POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_TREE_DEPTH <- PCQF_E010; POOL_V1_LEAF_CAPACITY <- PCQF_E004; M31.to_le_bytes <- PCWM_E001. Text is verbatim.
import Aeneas
import {G}.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace {G}
namespace PRVFresh_{G}_Funs_w1
/-- fresh type aspis_core::field::M31 (frozen Types text: `def field.M31 := Std.U32`) -/
@[reducible] def field.M31 := Std.U32
'''
th=f'''
end PRVFresh_{G}_Funs_w1
end {G}

namespace PRVEq.{G}.Funs_w1
open {G}

theorem pool_v1.POOL_V1_TREE_DEPTH : {G}.PRVFresh_{G}_Funs_w1.pool_v1.format.POOL_V1_TREE_DEPTH = {G}.pool_v1.POOL_V1_TREE_DEPTH := by
  unfold {G}.PRVFresh_{G}_Funs_w1.pool_v1.format.POOL_V1_TREE_DEPTH {G}.pool_v1.POOL_V1_TREE_DEPTH; rfl
#print axioms pool_v1.POOL_V1_TREE_DEPTH

theorem pool_v1.POOL_V1_DIGEST_ENCODING_VERSION : {G}.PRVFresh_{G}_Funs_w1.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION = {G}.pool_v1.POOL_V1_DIGEST_ENCODING_VERSION := by
  unfold {G}.PRVFresh_{G}_Funs_w1.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION {G}.pool_v1.POOL_V1_DIGEST_ENCODING_VERSION; rfl
#print axioms pool_v1.POOL_V1_DIGEST_ENCODING_VERSION

theorem VALUE_LIMIT : {G}.PRVFresh_{G}_Funs_w1.spend.VALUE_LIMIT = {G}.VALUE_LIMIT := by
  unfold {G}.PRVFresh_{G}_Funs_w1.spend.VALUE_LIMIT {G}.VALUE_LIMIT; rfl
#print axioms VALUE_LIMIT

/-- the fresh capacity is `1 <<< fresh TREE_DEPTH`, the gate's is `1 <<< gate TREE_DEPTH`; equal by the depth equality -/
theorem pool_v1.POOL_V1_LEAF_CAPACITY : {G}.PRVFresh_{G}_Funs_w1.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY = {G}.pool_v1.POOL_V1_LEAF_CAPACITY := by
  unfold {G}.PRVFresh_{G}_Funs_w1.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY {G}.pool_v1.POOL_V1_LEAF_CAPACITY
  rw [pool_v1.POOL_V1_TREE_DEPTH]
#print axioms pool_v1.POOL_V1_LEAF_CAPACITY

theorem aspis_core.field.M31.to_le_bytes : @{G}.PRVFresh_{G}_Funs_w1.field.M31.to_le_bytes = @{G}.aspis_core.field.M31.to_le_bytes := by
  rfl
#print axioms aspis_core.field.M31.to_le_bytes

end PRVEq.{G}.Funs_w1
'''
open(f'PRVEq_{G}_Funs_w1.lean','w').write(hdr+fresh+th)
