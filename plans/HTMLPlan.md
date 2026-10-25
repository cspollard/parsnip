# HTML and CSS support: design and status

Both formats are implemented as strict subsets with the same guarantee as
JSON and XML: a well-formed-by-construction AST, a tokenizer, a
fuel-bounded recursive-descent parser, and proved right inverses
(`parse (print x) ≡ x`, also as stdlib `RightInverse` stages), all
`--safe --cubical-compatible`, no postulates, depending only on
`standard-library`.

## What "support" means

We prove that parsing the printed text gives back the value. We do **not**
claim to accept everything a browser accepts. The core parsers are *strict*:
they read the canonical serialization the printers write. Lenient layers
(HTML tree construction, CSS error recovery, case folding, comments,
named entities) are out of scope and unproved.

## Shared infrastructure (extracted while building CSS)

| Module | Used by |
|---|---|
| `Data.Lexer` (`TokenLang`, generic `tokenize`/`lexer`, one theorem) | XML, JSON, CSS, HTML |
| `Data.Lexer.Span`, `Data.Lexer.Whitespace` | XML, JSON, CSS |
| `Data.Escape` (table-driven escaping + round-trip theorem) | XML, CSS, HTML (via XML) |
| `Data.Number.Digits` | JSON, CSS |
| `Data.Char.Class` (`isValidChar`, ranges) | XML, CSS, HTML |
| `Data.Sanitize` (`fixWith`, `fixText`, …) | XML, CSS, HTML |

## CSS (done)

Two levels, following CSS Syntax 3.

**Level 1, component values** (`Data.CSS.*`): `Valid` (character classes),
`Number`, `Escape`, `Token` (tokens and their lexer, with the main prefix
round trip `lexToken-printToken`), `Lexer` (`cssLang`), `AST`
(`CV = leaf | paren | bracket | brace | func`, `CSS = List CV`), `Tokens`
(`insertSeps` puts the comment token `/**/` between tokens that would run
together; `dropComments` removes it), `Parser`, `Print`, `RoundTrip`
(`cssStage`, `parseCSSText-printCSS`). Evidence that leaves are well formed
is `T b` in the constructors; children are plain lists, so the round trip
is `≡`, not bisimilarity.

**Level 2, grammar on top** : `Rule` (qualified and at-rules, with
prelude conditions as evidence; `parseRuleList-printRules`), `Declaration`
(`name : value ;`; `parseDeclList-printDecls`), `Stylesheet` (text level:
`parseStylesheet-printStylesheet`), `Sanitize` (total constructors),
`Examples`.

Strict-subset limits (deliberate): no exponents in numbers (`1e3` is the
dimension `1` with unit `e3`), no escapes in identifiers, no `url(` token
(it is the function `url(` plus a string), no CDO/CDC, no line
continuation in strings, XML-legal characters only; single-quoted strings
are read but printed with double quotes; `!important` is part of a
declaration's value.

`Selector` (selector lists over component values:
type/universal, class, id, attribute, pseudo-class/element, functional
pseudo with raw arguments, four combinators; strict canonical form with no
white space around `>`, `+`, `~`, `,`; `parseSelectorList-print`) and `Style`
(`selectorRule`, with the prelude evidence proved for every selector, and
a few typed declarations: `color`, `display`, `margin`, …).

**Not done:** error recovery; selector specificity; typed values beyond
keywords and pixel lengths.

## HTML (done)

`Data.HTML.*`:

- `Valid`: lower-case XML names for tags and attributes; `voidTags`
  (`br`, `img`, …), `rawTags` (`script`, `style`), `preTags`; `noEndTag`
  (a raw body contains no `</`); `okVoid`, `okRaw`, `okElem`.
- `AST`: `Elem = void | raw | elem`, the last with mixed content as in
  `Data.XML.AST` (leading text, then each child with its trailing text, so
  adjacent texts are unrepresentable) but as plain lists, so equality is
  `≡`. Kind-specific conditions are constructor evidence: `br` cannot
  have children, `script` has one raw body, a `pre` does not start with a
  newline.
- `Token`: an HTML token is an XML token (`Data.XML.Token`) or `rawT`, a
  whole raw-text element whose body is read up to the first `</`. The XML
  lexer and its proofs are reused; void elements print as `<br />`.
- `Lexer` (`htmlLang`, an instance of `Data.Lexer`), `Tokens`
  (`tokensElem`, `elem-run`: the stream is valid), `Parser`
  (`parseTokens-tokensElem`), `Print` (`printHTML` writes
  `<!DOCTYPE html>` first), `RoundTrip` (`htmlStage`,
  `parseBody-printBody`, `parseHTML-printHTML`), `Sanitize`
  (`element`: total constructor choosing the kind from the tag),
  `Elements` (vocabulary), `Examples`.
- Escaping is `Data.XML.Escape` unchanged (HTML decodes the same
  numeric/predefined entities).

Strict-subset limits: no comments, no doctype other than `html`, no
named entities beyond the five predefined, no foreign content, no HTML5
tree-construction rules (`<p><div>` etc. are accepted and printed
literally; whether a browser would read the same tree back is not
verified); a raw body may not contain `</` (`Sanitize.element` then makes
the body empty).

**Not done:** named entities (decode-only), `Normalize` (a lenient
layer), `SpecStable` (the content-model subset where browsers agree
with the tree), the `style=` attribute ↔ declarations, selector
matching. (`Data.HTML.Style` does the `<style>` element: partial, since
printed CSS may contain `</`.)

## Possible next steps

1. Selector specificity and matching against `Data.HTML.AST`.
2. Make `styleElement` total by printing a comment between `<` and `/`.
3. Named entities, a lenient normalizer, `SpecStable`.
