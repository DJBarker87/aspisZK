import Aeneas.Std.Core.Fmt

/-! Require the existing research formatter-repair profile, with an explicit
carrier definition and no extra type axiom. -/
namespace R1Z.PV_Src_FormatterAudit
abbrev formatter := Aeneas.Std.core.fmt.Formatter

theorem carrier : formatter = Unit := rfl

#print axioms formatter
#print axioms carrier
end R1Z.PV_Src_FormatterAudit
