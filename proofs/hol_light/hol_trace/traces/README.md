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

Only the README files are checked in: pruned traces take 0.08 to 13 GB
per function, 57 GB for all of them. How to store and share them is
still open, and no CI job currently downloads or checks them.
