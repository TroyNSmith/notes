#set par(justify: true)
#show link: underline
#import "@preview/physica:0.9.7"
#set math.equation(numbering: "(1)", number-align: bottom)
#let hfrac(a, b) = math.frac(a, b, style: "horizontal")
#let sfrac(a, b) = math.frac(a, b, style: "skewed")

// Theorem-like environments.
// Each kind is a distinct figure kind, so each gets its own independent counter.
// `emph` controls whether the statement is italicized.
#let env-kinds = (
  definition: (supplement: [Definition], emph: false),
  lemma: (supplement: [Lemma], emph: true),
  proposition: (supplement: [Proposition], emph: true),
  theorem: (supplement: [Theorem], emph: true),
  corollary: (supplement: [Corollary], emph: true),
  remark: (supplement: [Remark], emph: false),
)

// Proof display: "footnote" or "inline". Applies to all subsequent blocks:
//   #proof-mode.update("inline")
// Individual blocks can override this with `proof-style: "inline"` (or "footnote").
#let proof-mode = state("proof-mode", "footnote")
#let todo = text(fill: red)[*TODO*]

#let theorem-envs(doc) = {
  show figure: it => if type(it.kind) == str and it.kind in env-kinds {
    set align(start)
    rect(width: 100%, it.caption)
  } else { it }
  show figure.caption: it => if type(it.kind) == str and it.kind in env-kinds [
    #set text(size: 10pt)
    *#it.supplement #context it.counter.display(it.numbering).* #it.body
  ] else { it }
  doc
}

#let env(kind) = (statement, title: none, proof: none, proof-style: auto) => figure(
  kind: kind,
  supplement: env-kinds.at(kind).supplement,
  caption: context {
    set math.equation(numbering: none)
    let body = if env-kinds.at(kind).emph { emph(statement) } else { statement }
    let mode = if proof-style == auto { proof-mode.get() } else { proof-style }
    if title != none [_*#title.*_]
    if proof != none and mode == "footnote" { footnote[_Proof:_ #proof] }
    [ ]
    body
    if proof != none and mode == "inline" [
      #parbreak()
      _Proof._ #proof #h(1fr) $square$
    ]
  },
  [],
)

#let definition = env("definition")
#let lemma = env("lemma")
#let proposition = env("proposition")
#let theorem = env("theorem")
#let corollary = env("corollary")
#let remark = env("remark")

#show: theorem-envs



$
a + b - c
$

// To show all subsequent proofs inline instead of as footnotes:
// #proof-mode.update("inline")

#definition(
  [
    Here is some text defining something.
    $
    a + b = c
    $
  ],
  title: "My Definition",
) <def:example>

#proposition(
  [
    $
    a + b = c
    $
  ],
  title: "My Proposition",
  proof: [
    My proof here
  ],
) <prop:example>

#theorem(
  [
    Here is some text.
    $
    a + b = c
    $
  ],
  title: "My Theorem",
  proof: [
    My inline proof here
  ],
  proof-style: "inline",
) <thm:example>

This is seen in @def:example, @prop:example, and @thm:example[].
