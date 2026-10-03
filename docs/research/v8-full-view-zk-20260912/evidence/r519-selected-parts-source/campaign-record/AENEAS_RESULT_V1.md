# R519 literal-read translation attempt V1

The first direct-operand candidate used JSON tag `Constant`; pinned Charon accepts `Const`. Aeneas/Charon rejected the candidate during LLBC deserialization at `operand_of_json`, before translation. Exit 1; wall 0.16 s; peak RSS 82,472 KiB; swap 0. The full log is under `saved-output-literal-reads/`. This is a malformed serialization attempt, not a proof or source-semantics result.

V1 candidate SHA-256: `ed7ec2337267ab761c11aca1ad0a177c4ee9fa7528cc9087298b89a80c857100`.
Pinned Charon `Generated_OfJson.ml` SHA-256: `873cc528d0f3af4d63d79e444e2e733abcfbd97cdf59ba6da9390d89c3f19a3e`; its `operand_of_json` accepts `Const` and converts that form to internal `Constant`. The same R508 source capture has 55 ordinary `Const` operands in Fun18 with inline `{kind, ty}` expression shape.
