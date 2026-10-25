# parsnip

Verified printers and parsers for JSON, XML, CSS and HTML (and an SVG vocabulary), with
proved right inverses: `parse (print x) ≈ x`.  Container free-monad ASTs that
rule out ill-formed documents, tokenizers, fuel-bounded recursive-descent
parsers, and stdlib `RightInverse` stages (`Data.Stage`).

- `Data.JSON.*` — AST, tokens, lexer, parser, `Data.JSON.RoundTrip.jsonStage`
- `Data.XML.*` — AST, escaping, tokens, lexer, parser, `Data.XML.RoundTrip.xmlStage`
- `Data.CSS.*` — component-value syntax (tokens, lexer, parser,
  `Data.CSS.RoundTrip.cssStage`), rules (`Data.CSS.Rule`), declaration lists
  (`Data.CSS.Declaration`), `Data.CSS.Stylesheet`, total constructors
  (`Data.CSS.Sanitize`), `Data.CSS.Examples`
- `Data.HTML.*` — AST (void / raw-text / mixed-content elements), tokens,
  lexer, parser, `Data.HTML.RoundTrip.htmlStage`, total constructors
  (`Data.HTML.Sanitize`), vocabulary (`Data.HTML.Elements`),
  `<style>` elements from style sheets (`Data.HTML.Style`),
  `Data.HTML.Examples`
- `Data.SVG` — SVG elements over `Data.XML.Sanitize`
- `Data.Invertible.*` — invertible-syntax primitives
- `Data.Lexer` (generic tokenizer), `Data.Escape` (table-driven escaping),
  `Data.Sanitize`, `Data.Number.Digits`, `Data.Char.Class` — shared infrastructure
- `Data.Container.List`, `Data.Container.Pos`, `Data.Container.Table`, `Data.Stage` — shared
  infrastructure.  A node's children are indexed by `Pos n`, a number with an erased bound
  (not the unary `Fin n`), and lists become position functions through a balanced tree, so
  folding and building a node with `n` children is `O(n log n)`.
- `Data.Char.Fast` — fast character equality and membership used by the lexers

Check: `./make-everything.sh`.  Depends only on `standard-library`
(`--safe --cubical-compatible`, no postulates).
