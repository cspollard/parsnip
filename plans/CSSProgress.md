# CSS implementation: progress note

Written when work was paused at the user's request. `./make-everything.sh`
was clean (no errors or warnings) at that point. Nothing is committed yet.

## Done

**Shared infrastructure** (new, reused by JSON, XML and CSS)
- `Data.Lexer`: generic `TokenLang` record plus `Lexing` module (`tokenize`,
  `tokenize-printList`, `ValidTokens`, `lexer`). It has a `skip` field for
  white-space-skipping formats. XML, JSON and CSS all instantiate it, and the
  old per-format tokenizers are gone.
- `Data.Escape`: table-driven escaping plus the generic round-trip theorem
  `RoundTrip.lex-escapeWith`. `Data.XML.Escape` and `Data.CSS.Escape` use it.
- `Data.Number.Digits`: digit and `printNat`/`printFraction` machinery
  extracted from `Data.JSON.Number`, which re-exports it.
- `Data.Lexer.Span` (`spanBy` and its prefix lemma) and `Data.Lexer.Whitespace`
  (`skipWS`, used by JSON and XML).
- `Data.Char.Class`: `inRange`, `is`, `range` and `isValidChar`, all moved
  out of `Data.XML.Valid`, which re-exports them.
- `printTokenList` in XML and JSON is now `concatMap printToken`.

**CSS Level 1: component-value layer, fully proved** (`src/Data/CSS/`)
- `Valid`: character classes (`Cls`, `classOf`) and ident/hash validity.
- `Number`, `Escape`, `Token` (token lexer and `lexToken-printToken`),
  `Lexer` (`cssLang`), `AST` (`CV`, `CSS = List CV`), `Tokens`
  (`insertSeps`, which inserts `/**/` between tokens that would run
  together), `Parser`, `Print`, `RoundTrip`.
- Headline results: `cssStage : RightInverse (setoid CSS) Chars` and
  `parseCSSText-printCSS : parseCSSText (printCSS v) ≡ just v`.
- A smoke-test driver (compiled with MAlonzo) round-tripped a real
  stylesheet. It lives in the scratchpad, not in the repo.

**Plan**: `plans/HTMLPlan.md` now says CSS comes first. Its phase table
and CSS section are *not yet updated* to match what was built.

## Done since the pause (all building clean)

- `Data.Sanitize`: shared `fromEq`, `both`, `fixWith(-ok)`, `all-map`,
  `fixText(-valid)`; `Data.XML.Sanitize` uses it.
- `Data.CSS.Sanitize`: total constructors (`ident`, `atKeyword`, `hash`,
  `string`, `dimension`, `function`, `delim`, `number`, `percentage`,
  `whitespace`, `colon`, `semicolon`, `comma`) that repair bad input.
- `Data.CSS.Rule`: `Rule` (qualified / at-rule, with `T` evidence on the
  preludes), `printRules`, fuel-bounded `parseRules`, and
  `parseRuleList-printRules`.
- `Data.CSS.Stylesheet`: `parseStylesheet-printStylesheet` (text level).

- `Data.CSS.Declaration`: `Decl` (`name : value ;`, `!important` stays in
  the value), `parseDeclList-printDecls`.
- `Data.CSS.Examples`, README updated.

- HTML implemented (`Data.HTML.*`, see `plans/HTMLPlan.md`, which now
  describes the built design for both formats).

## Next steps (all optional)

1. Done: `Data.CSS.Selector` and `Data.CSS.Style`. Remaining: specificity, matching, more typed values.
2. `Data.HTML.Style` is done for `<style>` elements (partial); `style=` attribute ↔ declarations remains.
3. HTML: named entities, lenient normalizer, `SpecStable`.

## Design notes worth remembering

- All character reasoning goes through `Cls`/`classOf`. The digit test comes
  first, so any class other than `digitC` means `parseDigit c ≡ nothing`.
- `okFollow` is a deliberately conservative table: a token may be followed by
  a next token whose first character is of class `k` only if the table allows
  it. When it forbids a pair, the printer inserts `commentT`.
- Strict-subset limitations (on purpose): no exponents in numbers
  (`1e3` lexes as dimension `1` with unit `e3`), no escapes in identifiers,
  no `url(...)` token (it is the function `url(` plus a string), no
  CDO/CDC, no line continuation in strings, XML-legal characters only.
- Functions that dispatch on a `Bool` argument must have that `Bool` as the
  first pattern (see `lexSlash₁`), otherwise they get stuck on a variable
  list in proofs.
- The git working tree is dirty and uncommitted. Commit only when asked.
