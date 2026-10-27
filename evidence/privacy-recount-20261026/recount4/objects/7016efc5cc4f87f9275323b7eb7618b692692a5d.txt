# Early reservation retry retained

The public-record Kani preflight was refused at 22:40:43.349295 UTC. The
three-minute retry boundary was therefore 22:43:43.349295 UTC. I launched the
next client at 22:43:12 UTC; the admitted scope's ActiveEnterTimestamp was
22:43:15 UTC, about 28 seconds before the full wait boundary. This violated
the required three-minute wait. It is not concealed or recorded as a refusal:
the run is charged normally, its own receipt/result retained, memory/task caps
unchanged. No unchanged replacement verification will be run.

The task Kani client now checks prior denied reservation receipt timestamps
before any host action and returns an uncharged local hold until 180 seconds
have elapsed. This modifies no host launcher, scanner, quiet marker or cap.
The active run is allowed to reach its existing 120-second bound; no cap or
verification source was changed during it. The next queued target can only
launch after this scope is inactive and the guard passes.
