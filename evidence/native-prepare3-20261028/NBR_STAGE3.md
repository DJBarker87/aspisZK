# Stage 3: construct the opening and query observations

NBR_BlockConstruct, NBR_OpeningConstruct, NBR_MaterialConstruct and NBR_QueryConstruct construct the existing NBL local traces from the same infallible Digest32, S2/root/round1 view and fixed empty query state. NBR_VecAppend derives exact U8 cloning and concatenation from the actual selected std definitions, including their capacity bounds. Opening round1 size224 is required and is already derived by NBL_ViewDomains on the full proof domain. No stronger native caller precondition is introduced. These are model trace constructors, not a Rust interpreter theorem.

Accepted attempts L003/L010/L012/L014/L015; all printed roots use only standard axioms. Retained failed diagnostics L004/L007-L009/L011/L013 receive no credit. L005/L006 only inspect definitions.

K002 proves native arbitrary-row semantic shape/offset/bounds with no stubs. K001 selected a wrong harness path and ran no harness; K002 corrects the own input. K003 proves native canonical_scan's SAME464-byte check cut and rejection routing; arbitrary callee Results overapproximate the child, paired with CLOSED check_values on the proved domain. The echeck cut stops before executing its body. No field stubs or copy-dependent native credit here. K004's native TX1 caller cut timed out and remains excluded; see review. No timeout/cap increase or unchanged retry.
