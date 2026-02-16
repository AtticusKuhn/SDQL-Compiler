#import "@preview/typslides:1.3.2": *
#import "@preview/oxdraw:0.1.0": *


// Project configuration
#show: typslides.with(
  ratio: "16-9",
  theme: "bluey",
  font: "Fira Sans",
  font-size: 20pt,
  link-style: "color",
  show-progress: true,
)

// The front slide is the first slide of your presentation
#front-slide(
  title: "SDQL Compiler in Lean",
  subtitle: [Supervised by Neel Krishnaswami],
    authors: "Attics Kuhn (ak2518)",
  info: [#link("https://github.com/AtticusKuhn/SDQL-Compiler")],
)

// Custom outline
#table-of-contents()

// Slide with title
#slide(title: "Work Completed", outlined: true)[
#figure(
  image("sdql_dsl.png", height: 80%),
  caption: [
      A DSL for SDQL in Lean
  ],
)
]
#slide(title: "Work Completed", outlined: true)[
#figure(
  image("rust_code_generation.png", height: 80%),
  caption: [
      Rust Code Generation
  ],
)
]


// Slide with title
#slide(title: "Work Schedule", outlined: true)[
#table(
  columns: (auto, auto),
  inset: 10pt,
  align: horizon,
  table.header(
     [*Original Task*], [*Progress*],
  ),
    "project core (SDQL compiler)", $ballot.check.heavy$,
    "algebraic rewrite optimisation", $ballot.check.heavy$,
    "graph path fixpoint", $ballot.cross$,
)
]


#slide(title: "Unexpected Difficulties", outlined: true)[
#figure(
  image("difficulties.png", width: 100%),
  caption: [
    Writing to the original paper authors
  ],
)
]

// Bibliography
// #let bib = bibliography("bibliography.bib")
// #bibliography-slide(bib)
