#import "@preview/polylux:0.3.1": *
#import themes.metropolis: *
#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge

#show: metropolis-theme.with(footer: "")
#set text(size: 25pt)

#let beh = math.sans("beh")

#title-slide(
  title: "something coalgebra büchi automata",
  subtitle: "Research Internship Presentation",
  author: "Jorrit de Boer",
  date: "17 January 2025",
)

#new-section-slide("intro")
#slide(title: "Intro")[
  #metropolis-outline
]

#new-section-slide("Büchi automata")
#slide(title: "Büchi Automata")[
  #align(center)[
    #figure(
      diagram(
        node((0, 0), [`idle`], name: <x0>, shape: circle, stroke: .5pt, width: 3.5em, extrude: (0, -10)),
        node((2, 0), [`running`], name: <x1>, shape: circle, stroke: .5pt, width: 3.5em),
        node((-.75, 0), [], name: <x-1>),
        edge(<x0>, <x1>, [`request`], "->", bend: +20deg),
        edge(<x1>, <x1>, [`process`], "->", bend: -130deg, loop-angle: 180deg),
        edge(<x1>, <x0>, [`return`], "->", bend: +20deg),
        edge(<x-1>, <x0>, "->"),
      ),
      // caption: [Example of a Büchi automaton.],
    ) <img:buchi>
  ]
]

#new-section-slide("Coalgebra")

#slide(title: "Final Coalgebra Finite Automata")[
  very nice
  $
    #diagram(
  // spacing: 2cm,
  {
    node((0, 0), $2 times X^Sigma$, name: <FX>)
    node((0, 1), $X$, name: <X>)
    node((1, 0), $2times (2^Sigma^*)^Sigma$, name: <FZ>)
    node((1, 1), $2^Sigma^*$, name: <Z>)

    edge(<X>, <FX>, $angle.l o,delta angle.r$, "->", label-side: left)
    edge(<Z>, <FZ>, $angle.l e,d angle.r$, "->")
    edge(<X>, <Z>, $beh$, label-side: right, "->")
    edge(<FX>, <FZ>, $id times beh^Sigma$)
  },
)
  $
]

#slide(title: "ND system")[

  // #align(center)[
  #figure(
    diagram(
      spacing: 2em,
      node((0, 0), [$x_0$], name: <x0>, shape: circle, stroke: .5pt),
      node((1, 0), [$x_1$], name: <x1>, stroke: .5pt, shape: circle),
      node((0, 1), [$x_2$], name: <x2>, stroke: .5pt, shape: circle),
      node((1, 1), [$checkmark$], name: <check>),
      edge(<x0>, <x1>, [$a$], "->"),
      edge(<x0>, <x2>, [$a$], "->"),
      edge(<x2>, <x2>, [$c$], "->", bend: +130deg, loop-angle: 180deg),
      edge(<x1>, <x1>, [$b$], "->", bend: -130deg, loop-angle: 180deg),
      edge(<x1>, <check>, "->"),
      edge(<x2>, <check>, "->"),
    ),
    caption: [Example of a nondeterministic system.],
  ) <img:nd>

  not very nice coalgebra... because stupid Lambek
]

#slide(title: "Solution by Hasuo et al.")[
  $
    #diagram(
    // spacing: 2cm,
    {
      node((0, 1), $X$, name: <X>)
      node((0, 0), $overline(F) X$, name: <FX>)
      node((1, 1), $A$, name: <A>)
      node((1, 0), $overline(F) A$, name: <FA>)
      edge(<X>, <FX>, $c$, "->", label-side: left)
      edge(<A>, <FA>, $tilde.equiv$, "-", label-side: left, stroke: 0pt)
      edge(<A>, <FA>, $J alpha^(-1)$, "->", label-side: right)
      edge(<X>, <A>, $tr_c$, "-->", label-side: right)
      edge(<FX>, <FA>, $overline(F)(text(tr)_c)$, "-->")
      node((2, .5), $italic("in") cal("Kl")(cal(P)).$)
    },
  )
  $
  is a solution but a lot more stuff is necessary...
]

#slide(title: "Possibly Infinite Behavior")[
  getting towards that solution
]

#slide(title: "Büchi Automata final Coalg")[
  yay kind of solution
]

#slide(title: "Using Game Semantics to derive")[
  outline this? steps and saying these things are possible?
]

#new-section-slide("Conclusion")

#slide(title: "wrap up")[

]
