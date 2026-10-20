# Release notes

## Unreleased

- `Bool` is now recognized specially by generated runtime wrappers and maps to
  Nim `bool`. Rename a custom Eponym type that used the name `Bool` to avoid
  the new interpretation.
