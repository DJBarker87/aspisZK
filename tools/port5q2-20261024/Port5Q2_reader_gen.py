#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/port5q2-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(E/'reader-helpers/Funs.lean').read_text();a=s.index('def verifier.read_checkpoint_semantic_alpha');b=s.index('\nend Port5Q2_ReaderHelpers',a)
body=s[a:b].replace('def verifier.read_checkpoint_semantic_alpha','def semantic (read : CheckpointBytes4Sections.ReadK)').replace('verifier.Reader.k','read')
out='''import Port4A_ReaderInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderSemantic
open Aeneas Aeneas.Std Result AspisR1Stage2
'''+body+'''

/-- Kernel-checked normalization of CURRENT emitted helper, for every read
implementation, including all field-decoder errors and cursor returns. -/
theorem normalization (read : CheckpointBytes4Sections.ReadK) (bytes : Slice U8) (start : Usize) :
    semantic read bytes start=CheckpointBytes4Ops.semanticUsing read bytes start := by
  unfold semantic CheckpointBytes4Ops.semanticUsing CheckpointBytes4Ops.withK
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair0 success0
  rcases pair0 with ⟨value0,reader0⟩
  cases value0 with
  | Err e => rfl
  | Ok x0 =>
    try dsimp only
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro pair1 success1
    rcases pair1 with ⟨value1,reader1⟩
    cases value1 with
    | Err e => rfl
    | Ok x1 =>
      try dsimp only
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro pair2 success2
      rcases pair2 with ⟨value2,reader2⟩
      cases value2 with
      | Err e => rfl
      | Ok x2 =>
        try dsimp only
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
        apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro pair3 success3
        rcases pair3 with ⟨value3,reader3⟩
        cases value3 with
        | Err e => rfl
        | Ok x3 =>
          try dsimp only
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
          apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
          intro pair4 success4
          rcases pair4 with ⟨value4,reader4⟩
          cases value4 with
          | Err e => rfl
          | Ok x4 =>
            try dsimp only
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
            apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
            intro pair5 success5
            rcases pair5 with ⟨value5,reader5⟩
            cases value5 with
            | Err e => rfl
            | Ok x5 =>
              try dsimp only
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
              apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
              intro pair6 success6
              rcases pair6 with ⟨value6,reader6⟩
              cases value6 with
              | Err e => rfl
              | Ok x6 =>
                try dsimp only
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
                apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
                intro pair7 success7
                rcases pair7 with ⟨value7,reader7⟩
                cases value7 with
                | Err e => rfl
                | Ok x7 =>
                  try dsimp only
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
                  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
                  intro pair8 success8
                  rcases pair8 with ⟨value8,reader8⟩
                  cases value8 with
                  | Err e => rfl
                  | Ok x8 =>
                    try dsimp only
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
                    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
                    intro pair9 success9
                    rcases pair9 with ⟨value9,reader9⟩
                    cases value9 with
                    | Err e => rfl
                    | Ok x9 =>
                      try dsimp only
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]

#print axioms normalization
end AspisR1.Port5Q2_ReaderSemantic
end
'''
p=L/'Port5Q2_ReaderSemantic.lean';p.write_text(out)
(E/'semantic-emission.json').write_text(json.dumps({'source':'reader-helpers/Funs.lean','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'span_start':a,'span_end':b,'span_sha256':hashlib.sha256(s[a:b].encode()).hexdigest(),'changes':['namespace/carriers reused from AspisR1Stage2','opaque Reader.k becomes explicit ReadK argument'],'module_sha256':hashlib.sha256(out.encode()).hexdigest(),'external_template_imported':False},indent=2)+'\n')
