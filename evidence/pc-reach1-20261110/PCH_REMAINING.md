# Remaining PCH obligations

Stage 1 authority is admitted and the exact deployed ELF reproduces. Stage 2 is PARTIAL: the compiler supergraph is fail-closed, but the source MIR templates have not been resolved into exact monomorphized caller/callee associations. Runtime handler bodies outside the three project IR modules remain unknown. Stage 3 validates evidence integrity and rejects mutations; it does not resolve these edges. Stage 4 makes no status change.

Every unresolved edge conservatively includes all candidates under (c-g)(5); none supports an exclusion. Source-span diagnostics are a census only. No claim is made about body semantics, source/model refinement or security closure.

## Next deliverable

An exact compiler instance association with generic substitutions, fn/closure/trait-object materialisations, drop and inlined scopes, and handler closure for the same deployed artifact. It must cross-check codegen absence before any candidate exclusion. No Kani or Lean is needed for the reachability audit; this job has zero allowances for those proofs. Shared-body observations go only to Stream A.

## Member-by-member disposition

| Row | Class | Inherited | Diagnostic codegen matches | Remaining obstacle |
|---|---|---|---:|---|
| POOL:001 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:002 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:003 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:004 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:005 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:006 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:007 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:008 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:009 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:010 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:011 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:012 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:013 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:014 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:015 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:019 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:022 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:026 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:032 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:033 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:036 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:041 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:042 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:043 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:047 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:056 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:057 | B | OPEN | 2 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:058 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:070 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:073 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:074 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:075 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:076 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:077 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:078 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:079 | C | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:080 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:081 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:082 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:083 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:084 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:085 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:086 | D | OPEN | 2 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:087 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:088 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:089 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:091 | C | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:092 | B | OPEN | 2 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:093 | B | OPEN | 2 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:094 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:095 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:096 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:097 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:098 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:100 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:102 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:104 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:106 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:107 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:108 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:109 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:110 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:111 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:112 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:113 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:114 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:115 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:116 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:117 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:118 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:119 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:120 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:121 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:122 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:123 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:124 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:125 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:126 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:127 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:128 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:129 | C | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:130 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:131 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:132 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:133 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:134 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:135 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:136 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:137 | C | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:138 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:139 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:140 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:141 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:142 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:143 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:144 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:145 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:146 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:147 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:148 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:149 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:150 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:154 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:155 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:156 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:157 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:158 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:159 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:160 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:163 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:164 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:165 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:168 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:169 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:172 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:173 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:174 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:175 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:176 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:177 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:178 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:179 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:180 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:181 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:182 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:184 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:185 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:186 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:187 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:188 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:189 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:191 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:194 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:195 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:196 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:198 | C | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:199 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:208 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:209 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:220 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:221 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:222 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:223 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:241 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:242 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:243 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:244 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:245 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:246 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:265 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:266 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:271 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:272 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:273 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:274 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:275 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:276 | A | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:277 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:278 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:279 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:280 | A | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:281 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:282 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:283 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:284 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:285 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:286 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:287 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:288 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:289 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:290 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:291 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:292 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:293 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:294 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:295 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:296 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:297 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:298 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:299 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:300 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:301 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:302 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:303 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:304 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:305 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:306 | D | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:307 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:308 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:309 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:310 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:311 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:312 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:313 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:314 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:315 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:316 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:317 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:318 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:319 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:320 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:321 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:322 | C | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:323 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:324 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:325 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:326 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:327 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:328 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:329 | C | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:330 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:331 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:332 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:333 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:334 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:335 | D | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:336 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:337 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:338 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:339 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:340 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:341 | C | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:342 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:343 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:344 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:345 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:346 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:347 | C | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:348 | D | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:349 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:350 | C | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:351 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:352 | D | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:353 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:354 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:355 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:356 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:357 | D | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:358 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:359 | D | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:360 | D | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:361 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:362 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:363 | C | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:364 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:365 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:366 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:367 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:368 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:369 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:370 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:371 | A | CLOSED | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:372 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:373 | D | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:374 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:375 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:376 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:377 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:378 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:379 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:380 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:381 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:382 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:383 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:384 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:385 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:386 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:387 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:388 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:389 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:390 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:391 | A | CLOSED | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:392 | B | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:393 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:394 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:395 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:396 | D | OPEN | 1 | Codegen name association exists; exact MIR caller/callee substitution is missing; unresolved runtime/indirect closure prevents exclusion. |
| POOL:397 | B | OPEN | 0 | Exact source-to-instance association is missing; unresolved runtime/indirect closure prevents exclusion. |
