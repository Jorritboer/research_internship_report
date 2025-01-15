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

#slide(title: "Introduction")[
  #uncover("2-")[
    Outline:
    + Büchi Automata
    + Coalgebra Determinstic Finite Automata
    + Coalgebra Nondeterministic Finite Automata
    + Coalgebra Possibly Infinite Behavior Nondeterministic Finite Automata
    + Coalgebra Büchi Automata
    + Outline Derivation using Game Semantics
  ]
]

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

#slide(title: "Solution by Hasuo, Jacobs, Sokolova 2007")[
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

#slide(title: "Lifted Functor in Kleisli Category")[
  Model NFA $angle.l S, Sigma, delta, o angle.r$ by coalgebra $c: S -> 1 + Sigma times S$ for the functor $F S = 1 + Sigma times S$, which is $c: S -> cal(P)(1 + Sigma times S)$ in *Sets*.

  #uncover("2-")[
    Problem: a map $f: X -> Y$ in $Klp$ is $f: X -> cal(P)(Y)$ in *Sets* so $F f: F X -> F cal(P)(Y)$
  ]

  #uncover("3-")[
    We need a natural transformation $lambda: F cal(P) => cal(P)F$ (distributive law):

    $
      1 + Sigma times (cal(P)(S)) ->^lambda cal(P)(1 + Sigma times X)
    $
  ]

  #uncover("4-")[
    - $* arrow.r.bar {*} (1 = {*})$
    - $(sigma,S)={(sigma,x)|x in S}$ for $sigma in Sigma$ and $S subset.eq X$.

    For example: $delta(s)(sigma)={x,y,z}$ then $(lambda compose c)(s) = {(sigma,x),(sigma,y),(sigma,z)}$.
  ]

  #uncover("5-")[
    Call $overline(F) S = F S$ and $overline(F) f = lambda compose cal(P)(f)$ the _lifted functor_
  ]

]

#slide(title: [Initial Algebra $=>$ Final Coalgebra])[
  *Theorem* [Hasuo, Jacobs, Sokolova 2007]: An initial algebra $alpha: F A -> A$ for the functor $F$ in *Sets* yields the final coalgebra for $overline(F)$ in $Klp$:
  $
    (eta_(F A)compose alpha^(-1)) : A -> overline(F) A italic("in") Klp
  $

  #uncover("2-")[
    The initial algebra for $F S = 1 + Sigma times S$ is $[sans("nil"),sans("cons")]: 1 + Sigma times Sigma^* -> Sigma^* $:
    - $sans("nil")(*)=epsilon$
    - $sans("cons")(sigma, w)=sigma w$
    so we get $(eta_(1 + Sigma times S) compose [sans("nil"),sans("cons")]^(-1)): Sigma^* -> 1 +Sigma times Sigma^*$ ($Sigma^* -> cal(P)(1 + Sigma times Sigma^*)$ in *Sets*)
    - $(eta_(1 + Sigma times S) compose [sans("nil"),sans("cons")]^(-1))(epsilon)= {*}$
    - $(eta_(1 + Sigma times S) compose [sans("nil"),sans("cons")]^(-1))(sigma w)= {(sigma, w)}$
  ]
]

#slide(title: [Final Coalgebra Nondeterministic Automaton])[

  $
    #diagram(
    spacing: 3.5em,
    {
      node((0, 1), $S$, name: <X>)
      node((0, 0), $1 + Sigma times S$, name: <FX>)
      node((1, 1), $Sigma^*$, name: <A>)
      node((1, 0), $1 + Sigma times Sigma^*$, name: <FA>)
      edge(<X>, <FX>, $c$, "->", label-side: left)
      // edge(<A>, <FA>, $tilde.equiv$, "-", label-side: left, stroke: 0pt)
      edge(<A>, <FA>, $eta_(1+Sigma times Sigma^*) compose [sans("nil"),sans("cons")]^(-1)$, "->", label-side: right)
      edge(<X>, <A>, $text(tr)$, "-->", label-side: right)
      edge(<FX>, <FA>, $1 + Sigma times tr$, "-->")
      node((3, .5), $italic("in") cal("Kl")(cal(P)).$)
    },
  )
  $

  #uncover("2-")[
    $
      epsilon in tr(s) <==> * in c(s) <==> "state" s "is accepting"\
      sigma w in tr(s) <==> (sigma,w) in ((Sigma times beh) compose c)(s)={(sigma, beh(t)) | (sigma,t) in c(s)} <==> exists t. (t in delta(s)(sigma) and w in tr(t)).
    $ <eq:finite>
  ]
]

#slide(title: "Possibly Infinite Behavior")[
  *Theorem* [Jacobs 2004]: A final coalgebra $xi: Z -> F Z$ yields a _weakly final_ coalgebra
  $
    (eta_(F Z) compose xi) : Z -> overline(F)(Z) italic("in") Klp
  $

  #uncover("2-")[
    $
      #diagram(
    // spacing: 2cm,
    {
      node((0, 1), $S$, name: <X>)
      node((0, 0), $overline(F) S$, name: <FX>)
      node((1, 1), $Z$, name: <Z>)
      node((1, 0), $overline(F) Z$, name: <FZ>)
      edge(<X>, <FX>, $c$, "->", label-side: left)
      // edge(<Z>, <FZ>, $tilde.equiv$, "-", label-side: left, stroke: 0pt)
      edge(<Z>, <FZ>, $eta_(F Z) compose xi$, "->", label-side: right)
      edge(<X>, <Z>, $text(tr)$, "~>", label-side: right)
      edge(<FX>, <FZ>, $overline(F)(text(tr))$, "~>")
      node((2, .5), $italic("in") cal("Kl")(cal(P)),$)
    },
  )
    $
    $beh$ is not unique. However, we can take $beh^infinity$, the maximal mapping with respect to inclusion.
  ]
]

#slide(title: "")[
  $xi: Sigma^infinity -> 1 + Sigma times Sigma^infinity$ is the final $F$-coalgebra, defined by $xi(epsilon)& =* in 1$ and $xi(sigma w)&= (sigma,w)$ \ ($Sigma^infinity=Sigma^* union Sigma^omega$).

  #uncover("2-")[
    $
      #diagram(
    // spacing: 2cm,
    {
      node((0, 1), $S$, name: <X>)
      node((0, 0), $1 + Sigma times S$, name: <FX>)
      node((1, 1), $Sigma^infinity$, name: <A>)
      node((1, 0), [$1 + Sigma times Sigma^infinity$], name: <FA>)
      edge(<X>, <FX>, $c$, "->", label-side: left)
      edge(<A>, <FA>, $tilde.equiv$, "-", label-side: left, stroke: 0pt)
      edge(<A>, <FA>, $J xi$, "->", label-side: right)
      edge(<X>, <A>, $text(tr)^infinity_c$, "~>", label-side: right)
      edge(<FX>, <FA>, $1 + Sigma times tr^infinity_c$, "~>")
      node((2, .5), $italic("in") cal("Kl")(cal(P)).$)
    },
  )
    $

    $
      epsilon in tr^infinity (s) <==> * in c(s) <==> "state" s "is accepting" \
      sigma w in tr^infinity (s) <==> exists t. (s ->^sigma t and w in tr^infinity (t)).
    $ <eq:infinite>

  ]
]

#slide(title: "Büchi Automata Coalgebraically, Urabe, Shimizu, Hasuo 2016")[
  Idea: split $S=S_1 union S_2$ for $S_1$ non-accepting and $S_2$ accepting

  #uncover("2-")[
    $
      #diagram(
    spacing: 2.0cm,
    {
      node((0, 0), [$Sigma times S$], name: <fx1>)
      node((0, 1), [$S_1$], name: <x1>)
      node((1, 1), [$Sigma^omega$], name: <z1>)
      node((1, 0), [$Sigma times Sigma^omega$], name: <fz1>)
      edge(<x1>, <fx1>, $c_1$, "->", left)
      edge(<x1>, <z1>, $tr_1$, "~>", right)
      edge(<fx1>, <fz1>, $Sigma times [tr_1,tr_2]$, "~>")
      edge(<z1>, <fz1>, $eta_(Sigma^omega) compose  d$, right,"->")
      // edge(<z1>, <fz1>, $tilde.equiv$, "-", left, stroke: 0pt)

      node((2, 0), [$Sigma times S$], name: <fx2>)
      node((2, 1), [$S_2$], name: <x2>)
      node((3, 1), [$Sigma^omega$], name: <z2>)
      node((3, 0), [$Sigma times Sigma^omega$], name: <fz2>)
      edge(<x2>, <fx2>, $c_2$, "->", left)
      edge(<x2>, <z2>, $tr_2$, "~>", right)
      edge(<fx2>, <fz2>, $Sigma times [tr_1,tr_2]$, "~>")
      edge(<z2>, <fz2>, $eta_(Sigma^omega) compose d$, "->")
      // edge(<z2>, <fz2>, $tilde.equiv$, "-", left, stroke: 0pt)

      node((0.5,0.5), [$=_mu$])
      node((2.5,0.5), [$=_nu$])

      node((4.5, .5), $italic("in") cal("Kl")(cal(P)).$)
    },
  )
    $
  ]
  #uncover("3-")[
    $
      beh_1 &=^mu (eta_(Sigma^omega) compose d)^(-1) dot.circle overline(F)[beh_1,beh_2] dot.circle c_1 \
      beh_2 &=^nu (eta_(Sigma^omega)compose d)^(-1) dot.circle overline(F)[beh_1,beh_2] dot.circle c_2
    $
  ]
]

#set text(size: 15pt)
#slide(title: [Büchi Automata Coalgebraically, Urabe, Shimizu, Hasuo 2016])[
  #only((1, 2))[
    $
      beh_1 &=^mu (eta_(Sigma^omega) compose d)^(-1) dot.circle overline(F)[beh_1,beh_2] dot.circle c_1 #h(3em)
    beh_2 &=^nu (eta_(Sigma^omega)compose d)^(-1) dot.circle overline(F)[beh_1,beh_2] dot.circle c_2
    $
  ]
  #uncover("2-")[
    #only("2")[
      Rewrite to:]
    $
      beh_1 =^mu diamond_delta ([beh_1, beh_2]) harpoon.tr S_1 #h(3em) beh_2 =^nu diamond_delta ([beh_1,beh_2]) harpoon.tr S_2
    $

    Where $diamond_delta: (cal(P)(Sigma^omega))^(S)->(cal(P)(Sigma^omega))^(S)$ is given by
    $
      diamond_delta (beh)(s) = {sigma dot w | s'in delta(s)(sigma) , w in beh(s')}.
    $
  ]
  #uncover("3-")[
    *Definition*: The _solution_ to this _equational system_ is calculated as follows:
    - Intermediate solution $l^((1))_1 := mu u_1. f_1(u_1,u_2)$
    - $l^(sol):= nu u_2. f_2(l^((1))_1(u_2), u_2)$
    - $l^sol_1 = l^((1))_1(l^sol_2)$
  ]
  #uncover("4-")[
    Concretely:
    - $l^((1))_1 := mu u_1. diamond_delta ([u_1, u_2]) harpoon.tr S_1$
    - $l^(sol)_2:= nu u_2. u_2 diamond_delta ([mu u_1. diamond_delta ([u_1, u_2]) harpoon.tr S_1,u_2]) harpoon.tr S_2, u_2)$
    - $l^sol_1 = mu u_1. diamond_delta ([u_1, nu u_2. u_2 =^nu diamond_delta ([mu u_1^'. diamond_delta ([u_1^', u_2]) harpoon.tr S_1,u_2]) harpoon.tr S_2, u_2)]) harpoon.tr S_1$
  ]
]
#set text(size: 18pt)

#set text(size: 16pt)
#slide(title: "Büchi Automata Coalgebraically, Urabe, Shimizu, Hasuo. 2016")[
  Let $A=angle.l S, Sigma, delta, s_0, F angle.r$ be a Büchi automaton. Take $S_1=S backslash F$, $S_2=F$. Model $delta$ by coalgebras $c_1: S_1 -> cal(P)(Sigma times S)$, $c_2: S_2 -> cal(P)(Sigma times S)$. Take the initial algebra $d: Sigma^omega -> Sigma times Sigma^omega$ defined by $d(sigma w)=(sigma,w)$ in *Sets*.
  $
    #diagram(
    spacing: 2.0cm,
    {
      node((0, 0), [$Sigma times S$], name: <fx1>)
      node((0, 1), [$S_1$], name: <x1>)
      node((1, 1), [$Sigma^omega$], name: <z1>)
      node((1, 0), [$Sigma times Sigma^omega$], name: <fz1>)
      edge(<x1>, <fx1>, $c_1$, "->", left)
      edge(<x1>, <z1>, $tr_1$, "~>", right)
      edge(<fx1>, <fz1>, $Sigma times [tr_1,tr_2]$, "~>")
      edge(<z1>, <fz1>, $eta_(Sigma^omega) compose  d$, right,"->")
      // edge(<z1>, <fz1>, $tilde.equiv$, "-", left, stroke: 0pt)

      node((2, 0), [$Sigma times S$], name: <fx2>)
      node((2, 1), [$S_2$], name: <x2>)
      node((3, 1), [$Sigma^omega$], name: <z2>)
      node((3, 0), [$Sigma times Sigma^omega$], name: <fz2>)
      edge(<x2>, <fx2>, $c_2$, "->", left)
      edge(<x2>, <z2>, $tr_2$, "~>", right)
      edge(<fx2>, <fz2>, $Sigma times [tr_1,tr_2]$, "~>")
      edge(<z2>, <fz2>, $eta_(Sigma^omega) compose d$, "->")
      // edge(<z2>, <fz2>, $tilde.equiv$, "-", left, stroke: 0pt)

      node((0.5,0.5), [$=_mu$])
      node((2.5,0.5), [$=_nu$])

      node((4.5, .5), $italic("in") cal("Kl")(cal(P)).$)
    },
  )
  $
  $
    beh_1 =^mu diamond_delta ([beh_1, beh_2]) harpoon.tr S_1 #h(3em) beh_2 =^nu diamond_delta ([beh_1,beh_2]) harpoon.tr S_2
  $

  Where $diamond_delta: (cal(P)(Sigma^omega))^(S)->(cal(P)(Sigma^omega))^(S)$ is given by
  $
    diamond_delta (beh)(s) = {sigma dot w | s'in delta(s)(sigma) , w in beh(s')}.
  $

  #uncover(2)[
    *Theorem* [Urabe, Shimizu, Hasuo 2016]: The solutions $beh_1,beh_2$ to the system of equations coincide with the accepted language of the Büchi Automaton $A$.
  ]
]


#slide(title: "Alternate Proof of Coincidence Result")[
  Problem: system of fixed point equations is convoluted.

  #uncover("2-")[
    Alternate derivation using game semantics:\
    *Game Semantics Theorem*: $s scripts(tack.r.double)^T phi <==> $ verifier has a winning strategy in $cal(G)(phi, T)$

    Outline:
    - Convert system of equations to modal mu-calculus formula
    - Apply game semantics theorem
    - Prove: $V$ has a winning strategy in $cal(G)(phi,T)$ from state $(x_i,w)$ $ <==> w in beh(s_i)$
  ]
]

#slide(title: "Proof Outline")[
  #[Converting formula:
    $ l_sol^2 = nu u_2. diamond^2_delta [(mu u_1^'. diamond^1_delta [u_1^', u_2]), u_2] $

    $
      overline(phi_2)=nu u_2. (p_2 and diamond((mu u_1^'.p_1 and diamond((p_1 and u_1^') or (p_2 and u_2))) or (p_2 and u_2))))
    $
  ]
  #uncover("2-")[
    Defining Transition System for Büchi Automaton $A$:

    Let $A=(S_1 union S_2, Sigma, delta)$ be a Büchi automaton. Let Transition System (TS) over the set of propositional variables ${p_1,p_2}$, denoted as $T_A$, as follows:
    - States: $(s,w)$ for $s in S$ and $w in Sigma^omega$
    - Transition $(s,sigma w) -> (s', w)$ for $s,s'in S$, $sigma in Sigma$, $w in Sigma^omega$, iff $s'in delta(s)(sigma)$
    - Labeling function: $lambda((s,w))={p_i}$ iff $s in S_i$
  ]
  #uncover("3-")[
    *Game Semantics Theorem*: $(s,w) tack.r.double^T phi$ iff Verifier has a winning strategy in $cal(G)(phi,T_A)$ from state $(phi,(s,w))$
  ]

  #uncover("4-")[
    *Lemma*: Verifier has a winning strategy in $cal(G)(phi,T_A)$ from state iff the Büchi automaton accepts $w$ from $s$.
  ]
]
#set text(size: 18pt)

// #new-section-slide("Conclusion")

#slide(title: "Conclusion")[

  + Büchi Automata
  + Coalgebra Determinstic Finite Automata
  + Coalgebra Nondeterministic Finite Automata
  + Coalgebra Possibly Infinite Behavior Nondeterministic Finite Automata
  + Coalgebra Büchi Automata
  + Outline Derivation using Game Semantics

]
