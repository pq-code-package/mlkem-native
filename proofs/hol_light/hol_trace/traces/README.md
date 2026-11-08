[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Traces

`hol-trace` writes one set of files per function to `ARCH/`:

| File | Content |
|---|---|
| `FUNC.50` | HOLTrace trace (`FUNC.raw.50`: unpruned, while `gen` prunes) |
| `FUNC.manifest.json` | source hashes, main-theorem names, recording-package names, trace hash, time and memory |
| `FUNC.gen.log` | log of `gen` |
| `FUNC.BACKEND.result` | theory replayed by `BACKEND`, read by `compare` |
| `FUNC.BACKEND.replay.log` | log of `replay` |
| `FUNC.outline.result`, `FUNC.outline.log` | theory and log of `outline`, read by its own `compare --accept` only |

Only the README files are checked in: traces take up to many gigabytes
per function. CI records them afresh and does not keep them.
