The TX1 composition interface should consume JFx_NativeBytes.checkpoint,
not a newly encoded checkpoint or an independently chosen source cut.
The planned JFq_Prepared.value and accumulator are explicit field records
selected from that exact retained checkpoint. They do not assert TX1 saved
it. JFr_'s accepted1 and saved-Vec equality are still required for the joint
pair. The retained checkpoint hash is6c9f774dd0032d3df18c9724c38d02c5225f31808a4cfe8560c210dc4d3dc625.

TX2 then needs the installed query/flush, batch1 and finish on those exact
records and proof/public bytes. No full-wrapper acceptance fact follows
from source-reader normalization or individual field totality.
