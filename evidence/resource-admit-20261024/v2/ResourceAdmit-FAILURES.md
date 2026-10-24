# Retained v2 local failure

focused-v2: five groups, one failure. Direct local macOS Python launched after
env -i injected __CF_USER_TEXT_ENCODING. This is newly observed LOCAL test
behavior only, not a diagnosis of the old Linux child failure (differing field
still UNKNOWN). No host operations or epoch charge. No runtime/env exception
added. Replacement local check inspects env's direct output exactly, including
literal quoting/newline bytes; strict checker continues to deny all dirty maps.
Linux pinned Python remains subject to exact pre/go/post verification. Any
host runtime/environment mismatch will be terminal without retry.
