// Template for problem-set solutions.
//
// Usage:
//   #import "template/pset.typ": *
//   #show: pset.with(title: "Chapter 7 — Fourier Transforms")
//
//   =                          // Exercise 1 (empty heading = skipped)
//   =                          // Exercise 2
//   #statement[...]            // optional copy of the exercise text
//   + ...                      // parts: (a), (b), ... nested i., ii., ...
//   #claim[...] <my-claim>     // Claim 2.1, referenced by @my-claim
//   #proof[...]                // ends with ∎

#let page-style(body) = {
  set page(paper: "a4", margin: 2.5cm, numbering: "1")
  set text(font: "New Computer Modern", size: 11pt)
  set par(justify: true)
  body
}

// Each level-1 heading is an exercise, numbered automatically
#let exercise-headings(body) = {
  set heading(numbering: "1")
  show heading.where(level: 1): it => {
    counter(figure.where(kind: "thm")).update(0)
    block(above: 2em, below: 1em, text(size: 14pt)[
      *Exercise #counter(heading).display()*
      #if it.body != [] [— #it.body]
    ])
  }
  body
}

// (a), (b), ... then i., ii., ...
#let part-numbering(body) = {
  set enum(spacing: 1.2em, full: true, numbering: (..n) => {
    let n = n.pos()
    if n.len() == 1 { numbering("(a)", ..n) } else { numbering("i.", n.last()) }
  })
  body
}

#let theorem-style(body) = {
  show figure.where(kind: "thm"): it => block(width: 100%, above: 1.2em, below: 1.2em, align(left)[
    *#it.supplement #it.counter.display(it.numbering).* #it.body
  ])
  body
}

#let title-block(title) = {
  align(center, text(size: 1.6em, weight: "bold", title))
  v(1em)
}

#let pset(title: none, body) = {
  set document(title: title)
  show: page-style
  show: exercise-headings
  show: part-numbering
  show: theorem-style
  if title != none { title-block(title) }
  body
}

// Claims and lemmas share one counter, numbered per exercise (5.1, 5.2, ...)
#let _thm(supplement) = body => figure(
  body,
  kind: "thm",
  supplement: supplement,
  numbering: n => numbering("1.1", counter(heading).get().first(), n),
  outlined: false,
)

#let claim = _thm[Claim]
#let lemma = _thm[Lemma]

#let proof(body) = block(width: 100%, below: 1.2em)[
  _Proof._ #body #h(1fr) $square$
]

#let statement(body) = block(inset: (left: 1.5em), below: 1.2em, emph(body))

// Notation
#let ip(x, y) = $lr(chevron.l #x, #y chevron.r)$
