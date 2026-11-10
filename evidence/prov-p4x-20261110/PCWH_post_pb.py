#!/usr/bin/env python3
"""PCWH post-processing of the generated PRVEq_PB file for the second tool version. (1) drop the linter option unknown to the gate's Lean;
(2) library-version shim: the new Aeneas Lean library names Result::from_residual core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
(Never) where the gate's library names it ...CoreOpsTryTraitFromResidualResultInfallible.from_residual (Infallible); the bodies printed by PCWH_L002 (old) and read from
src/aeneas/backends/lean/Aeneas/Std/Core/Convert.lean (new) are the same definition (casesOn on the empty type; Err e => From.from e). The shim is a definition, not an axiom."""
import sys,re
s=open(sys.argv[1]).read()
s=re.sub(r'(?m)^set_option linter\.internalConstructors false\n','',s)
shim='''namespace Aeneas.Std
/-- PCWH library-version shim (see PCWH_post_pb.py): new-library name of Result::from_residual = gate-library constant. -/
abbrev core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual :=
  @core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
end Aeneas.Std

'''
import re as _re
i=_re.search(r'(?m)^namespace (?!Aeneas\.Std)',s).start()
s=s[:i]+shim+s[i:]
open(sys.argv[2],'w').write(s)
