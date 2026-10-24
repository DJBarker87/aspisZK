# Preserved failure

lean-001: new attribution used a module doc comment before import; Lean rejects import after that command. No replay ran. Corrected the comment to an ordinary source comment. One charged actual Lean attempt, exit 1, original snapshot/log/receipt retained. No resource-limit change.

lean-003: rejection callback inferred TermElabM, yielding exception ToString/MonadExcept errors. No test executed. Replacement explicitly types the callback as IO Unit; original failed source/receipt retained.
