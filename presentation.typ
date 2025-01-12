#import "@preview/polylux:0.3.1": *
#import themes.metropolis: *
#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge

#show: metropolis-theme.with(footer: "")
#set text(size: 18pt)

#let Run = text("Run")
#let AccRun = text("AccRun")
#let sol = text("sol")
#let Tree = text("Tree")
#let DelSt = text("DelSt")
#let beh = math.sans("beh")
#let Klp = $cal("Kl")(cal(P))$
#let tr = beh
#let lfp = text("lfp")
#let Var = math.italic("Var")
#let Prop = math.italic("Prop")
#let cons = math.sans("cons")
#let box = $square$

#title-slide(
  title: "Coalgebraic Representation of Büchi Automata",
  subtitle: "Research Internship Presentation",
  author: "Jorrit de Boer",
  date: "17 January 2025",
)

#new-section-slide("Büchi Automata")

#slide(title: "Büchi Automata")[
  // #text(size:18pt)[
  #align(center)[
    #figure(
      diagram(
        node((0, 0), [`idle`], name: <x0>, shape: circle, stroke: .5pt, width: 3.5em, extrude: (0, -12)),
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
  #side-by-side()[
    #uncover((2, 3, 4))[
      *Definition*:
      A (nondeterministic) _Büchi Automaton_ $A=angle.l S, Sigma, delta, s_0, F angle.r$, where:
      - $S$: finite set of states
      - $Sigma$: alphabet
      - $s_0 in S$: initial state
      - $delta : S times Sigma -> cal(P)(S)$: transition function
      - $F subset.eq S$: set of _final_ (or _accepting_) states.\
    ]][
    #uncover((3, 4))[
      A _run_ of $A$ on an $omega$-word $w=sigma_0 sigma_1... in Sigma^omega$ is an infinite sequence of states $s_0,s_1,... in S^omega$ such that for all $n$, $s_(n+1)in delta(s_n,sigma_n)$

      A run is _accepted_ if it visits $F$ infinitly often.

      #uncover(4)[
        Accepted language: $(mono("request") dot mono("process")^*dot mono("return"))^omega$
      ]
    ]
  ]
]

#new-section-slide("Coalgebra")

#slide(title: "Final Coalgebra Deterministic Finite Automata")[
  $angle.l S, Sigma, delta, o angle.r $ with states $S$, alphabet $Sigma$, transition function $delta:S times Sigma -> S$, $o: S -> 2$ ($2 = {0,1}$). Can be represented by a coalgebra $angle.l o, delta angle.r: S -> 2 times S ^ Sigma$ for functor $F S = 2 times S^Sigma$

  #uncover("2-")[
    The final coalgebra for $F$ is $angle.l e,d angle.r : 2^Sigma^* -> 2 times (2^Sigma^*)^Sigma$. Where
    - $e(L)=1$ iff $epsilon in L$
    - $d(L)(a)=L_a$ where $L_a (w)=L(a w)$ so $w in d(L)(a)$ iff $a w in L$
  ]

  #side-by-side()[
    #uncover("3-")[$#diagram(
  spacing: 2.5cm,
  {
    node((0, 0), $2 times S^Sigma$, name: <FX>)
    node((0, 1), $S$, name: <X>)
    node((1, 0), $2times (2^Sigma^*)^Sigma$, name: <FZ>)
    node((1, 1), $2^Sigma^*$, name: <Z>)

    edge(<X>, <FX>, $angle.l o,delta angle.r$, "->", label-side: left)
    edge(<Z>, <FZ>, $angle.l e,d angle.r$, "->", label-side: right)
    edge(<X>, <Z>, $beh$, label-side: right, "-->")
    edge(<FX>, <FZ>, $id times beh^Sigma$, "-->")
  },)$]][
    #uncover("4-")[
      Following the paths through the diagram we obtain:
      - $beh(s)(epsilon)=o(s)$, and
      - $beh(s)(sigma w)=beh(delta(s)(sigma))(w)$,

      #uncover("5-")[
        So $beh$ captures exactly the accepted language of the automaton!]]
  ]
]

#slide(title: "Nondeterministic Finite Automata")[
  #figure(
    diagram(
      // spacing: 2em,
      node((0, 0), [$s_0$], name: <x0>, shape: circle, stroke: .5pt),
      node((1, 0), [$s_1$], name: <x1>, stroke: .5pt, shape: circle, extrude: (0, -5)),
      node((0, 1), [$s_2$], name: <x2>, stroke: .5pt, shape: circle, extrude: (0, -5)),
      // node((1, 1), [$checkmark$], name: <check>, stroke: .5pt),
      edge(<x0>, <x1>, [$a$], "->"),
      edge(<x0>, <x2>, [$a$], "->"),
      edge(<x2>, <x2>, [$c$], "->", bend: +130deg, loop-angle: 180deg),
      edge(<x1>, <x1>, [$b$], "->", bend: -130deg, loop-angle: 180deg),
      // edge(<x1>, <check>, "->"),
      // edge(<x2>, <check>, "->"),
    ),
  ) <img:nd>

  Might be modeled by coalgebra $c: S -> 2 times cal(P)(Sigma times S)$.

  #uncover("2-")[
    A final coalgebra $z: Z -> 2 times cal(P)(Sigma times Z)$ cannot exist. Lambek's lemma says $z$ would have to be an isomorphism, which would imply $Z tilde.equiv cal(P)(Z)$
  ]
]

#slide(title: "Solution by Hasuo et al. 2007")[
  Kleisli Category of the monad $cal(P)$:

  A coalgebra $c: S -> Sigma times S$ in $Klp$ is $c: S -> cal(P)(Sigma times S)$ in *Sets*. #uncover("2-")[ Concretely:
    - $eta_X : X -> cal(P)(X)$: $eta_X (x)={x}$
    - $mu_X: cal(P)(cal(P)(X)) -> cal(P)(X)$: $mu_X (A) = union.big_(a in A) a$.

  For $f: X -> Y$, $cal(P)(f): cal(P)(X) -> cal(P)(Y)$ by $cal(P)(f)(A)= {f(a) | a in A}$

    - *objects*: the same as for *Sets*, sets
    - #[*morphisms*: $f: X -> Y$ in $Klp$ is $f:X-> cal(P)(Y)$ in *Sets*. \
        For morphisms $f: X -> Y$ and $g: Y -> Z$ in $Klp$ we define
        $
          g dot.circle f := X ->^f cal(P)(Y) ->^(cal(P)(g)) cal(P)(cal(P)(Z)) ->^(mu_Y) cal(P)(Z)
        $
      ]
  ]
]

#slide(title: "Solution by Hasuo et al. 2007")[
  Distributive law?

  Initial algebra in *Sets* is final coalgebra in $Klp$

  $
    #diagram(
    spacing: 3.5em,
    {
      node((0, 1), $S$, name: <X>)
      node((0, 0), $1 + Sigma times S$, name: <FX>)
      node((1, 1), $Sigma^*$, name: <A>)
      node((1, 0), $1 + Sigma times Sigma^*$, name: <FA>)
      edge(<X>, <FX>, $c$, "->", label-side: left)
      edge(<A>, <FA>, $tilde.equiv$, "-", label-side: left, stroke: 0pt)
      edge(<A>, <FA>, $eta_(1+Sigma times Sigma^*) compose [sans("nil"),sans("cons")]^(-1)$, "->", label-side: right)
      edge(<X>, <A>, $text(tr)$, "-->", label-side: right)
      edge(<FX>, <FA>, $1 + Sigma times tr$, "-->")
      node((3, .5), $italic("in") cal("Kl")(cal(P)).$)
    },
  )
  $

  $
    epsilon in tr(s) <==> * in c(s) <==> "state" s "is accepting"\
    sigma w in tr(s) <==> exists t. (s ->^sigma t and w in tr(t)).
  $ <eq:finite>
  Which are the right traces!
]

#slide(title: "Possibly Infinite Behavior")[ ]

#slide(title: "Büchi Automata final Coalg")[ ]

#slide(title: "Using Game Semantics to derive")[
  outline this? steps and saying these things are possible?
]

#new-section-slide("Conclusion")

#slide(title: "wrap up")[

]
