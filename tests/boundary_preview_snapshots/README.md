# Boundary preview snapshots

This suite elaborates each `.ep` fixture, computes the boundary report through
`boundaryPreviewReport`, and compares the string byte-for-byte. It never
compiles generated fixture output. Run the normal check with:

```text
nim c -r --hints:off --path:src --path:src/eponym tests/boundary_preview_snapshots.nim
```

After a deliberate report change, bless with `--bless`, inspect every diff,
then rerun without `--bless`. The fixtures cover a length-indexed `Vec`, a
dependent `Sig`, an opaque host mapping, a higher-order parameter, and the
interpreter/Value fallback path.
