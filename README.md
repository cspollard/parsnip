# parsnip

Verified printers and parsers for JSON and XML (and an SVG vocabulary), with
proved right inverses: `parse (print x) ≈ x`.  Container free-monad ASTs that
rule out ill-formed documents, tokenizers, fuel-bounded recursive-descent
parsers, and stdlib `RightInverse` stages (`Data.Stage`).

- `Data.JSON.*` — AST, tokens, lexer, parser, `Data.JSON.RoundTrip.jsonStage`
- `Data.XML.*` — AST, escaping, tokens, lexer, parser, `Data.XML.RoundTrip.xmlStage`
- `Data.SVG` — SVG elements over `Data.XML.Sanitize`
- `Data.Invertible.*` — invertible-syntax primitives
- `Data.Container.List`, `Data.Stage` — shared infrastructure

Check: `./make-everything.sh`.  Depends only on `standard-library`
(`--safe --cubical-compatible`, no postulates).
