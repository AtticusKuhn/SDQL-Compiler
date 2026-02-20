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

#slide(title: "Work Completed", outlined: true)[
#figure(
  image("rust_optimisation.png", height: 80%),
  caption: [
      Code Optimisations
  ],
)
]

#slide(title: "Work Completed", outlined: true)[
#figure(
  image("tpch.png", height: 80%),
  caption: [
      TPC-H test benchmark matches reference implementation
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
    "Writing up core", $ballot.cross$,
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

#show raw.where(block: true): set text(0.4em / 0.8)

#slide(title: "Unexpected Difficulties", outlined: true)[
    ```lean
CodegenRust.lean:126:4
Tactic `cases` failed with a nested error:
Dependent elimination failed: Failed to solve equation
  Ty.int.dict Ty.bool =
    Acc.rec
      (fun x₁ h ih ↦
        (fun a a_1 ↦
            (match (motive :=
                (a : _root_.Ty) → ((y : _root_.Ty) → (invImage (fun x ↦ x) sizeOfWFRel).1 y a → _root_.Ty) → _root_.Ty)
                a with
              | dom.dict range => fun x ↦ dom.dict (x range ⋯)
              | Ty.record l => fun x ↦
                Ty.record
                  (List.map
                    (fun x_1 ↦
                      match x_1 with
                      | ⟨t, h⟩ => x t ⋯)
                    l.attach)
              | x => fun x ↦ t2✝)
              a_1)
          x₁ ih)
      ⋯
at case `Term2.mul` after processing
  _, _, (Term2.sum _ Ty.int Ty.bool _ _ (TermLoc2.mk _ _ _ _) _)
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
```
]


// Bibliography
// #let bib = bibliography("bibliography.bib")
// #bibliography-slide(bib)
