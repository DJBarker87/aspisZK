
## Resume L248–L260 local repairs
L248/L260 and L256/L257 failed solely because final rfl followed a tactic
that had already solved the goal. The successful source-position cases were
retained, redundant tactics removed, and changed sources passed L251/L258/
L259/L261. L253/L254 generic emitted_try application was replaced by one
explicit outer/inner Result split per mapper occurrence; generic unification
shape is retired. No timeout, memory kill, cap increase, or unchanged failed
rerun occurred. L250 fixes the getter match iota reduction; L252 uses existing
RS.seq_pure/throw instead of broad observational unfolding.
