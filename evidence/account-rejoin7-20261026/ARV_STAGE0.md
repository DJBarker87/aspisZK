# ARV stage 0 — statement audit

Target not yet established. Branch codex/cx-account-rejoin7-20261026.
All required handoffs/rules inspected; historical paths resolve under docs/research/100bit-spend-path-20261013.
Only ARV_ modules and this evidence directory will be changed. No Kani or shipped edits.

The proposed self-cylinder argument has two nontrivial inputs: SupportedEntry and RuntimeSyscall at that world's native tuple. Partial acceptance does not definitionally provide either. Investigation targets an exact abstract account execution with invalid runtime admission; it must be explicitly distinguished from an approved deployed execution.

Reuse the coherent SInt2 objects and unchanged admission/launcher. 100 Lean invocations maximum, including dependency builds; one capped scope at a time. Every new public theorem gets an axioms audit.
