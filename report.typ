#import "@preview/fletcher:0.5.4" as fletcher: diagram, node, edge
#import "@preview/ctheorems:1.1.3": *

#show: thmrules.with(qed-symbol: $square$)

#let mythmbox(..args) = thmbox(..args, inset: (x: 1em))
#let mythmproof(..args) = thmproof(..args, inset: 0em)

#let theorem = mythmbox("theorem", "Theorem", base: "heading", base_level: 1)
#let lemma = mythmbox("theorem", "Lemma", base: "heading", base_level: 1)
#let definition = mythmbox("theorem", "Definition", base: "heading", base_level: 1, inset: 0em, breakable: true)
#let proof = mythmproof("proof", "Proof")
// #let theorem = thmbox("theorem", "Theorem", base:"heading", bodyfmt: body => [asdf])
// #let lemma = thmbox("theorem", "Lemma", base:"heading", bodyfmt: body => [#align(left)[#body]])
// #let definition = thmbox("theorem", "Definition", base:"heading", base_level: 1, bodyfmt: body => [#align(left)[#body]])
// #let proof = thmproof("proof", "Proof", bodyfmt: body => [#align(left)[#body]])

#let appendix(body) = {
  set heading(numbering: "A.1", supplement: [Appendix])
  counter(heading).update(0)
  body
}

#set text(size: 10pt)

#set math.equation(numbering: "(1)")

#set page(numbering: "1", number-align: center)

// definitions
#let Run = text("Run")
#let AccRun = text("AccRun")
#let sol = text("sol")
#let Tree = text("Tree")
#let DelSt = text("DelSt")
#let beh = math.sans("beh")
#let Klp = $cal("Kl")(cal(P))$
#let tr = beh
#let lfp = text("lfp")
#let gfp = text("gfp")
#let Var = math.italic("Var")
#let Prop = math.italic("Prop")
#let cons = math.sans("cons")
#let box = $square$


// Title row.
#align(center)[
  #text(
    20pt,
    weight: 700,
    "Alternate Derivation of the Coalgebraic Representation of Büchi Automata Using Game Semantics",
  )

  #text(14pt, weight: 600, "Research Internship Report")

  Jorrit de Boer
]

#set heading(numbering: "1.1")
#set par(justify: true)


#align(center)[
  #set par(justify: false)
  // #set text(style: "italic")
  *Abstract.*
  _We provide a review of existing literature for describing Büchi automata coalgebraically using trace semantics. To do this we also explain the modal $mu$-calculus and a coalgebraic model of nondeterministic systems. Finally, we present an alternate derivation of the coalgebraic model for Büchi automata using game semantics, which gives a new conceptual perspective on the existing coalgebraic framework.  _
]

= Introduction

_Büchi automata_ are crucial in theoretical computer science for modeling and verifying systems with infinite behaviors @gradel2003automata@Vardi1996. Büchi automata are generally nondeterminstic, allowing them to capture uncertainty and multiple outcomes @martin1991introduction. Because of their ability to capture nondeterminstism and handle infinite sequences of events, Büchi automata are crucial for verifying systems that run indefinitely, such as operating systems or network protocols.

_Coalgebra_ provides an abstract framework for modeling state-based, dynamic systems @rutten2000universal. Techniques such as _coinduction_ allow for reasoning about infinite structures, while _bisimulation_ offers a formal way to establish behavioral equivalence between systems. By modeling Büchi automata coalgebraically, these powerful tools can be applied for reasoning about infinite behaviors and nondeterminism.

The first goal of this report is to provide an understanding of the coalgebraic semantics using _trace semantics_ of Büchi automata described in @urabe2016coalgebraic. To do so we also explain the _modal $mu$-calculus_ @arnold2001rudiments, a system for verifying properties of transition systems, and a coalgebraic model of nondeterministic systems from @hasuo2007generic, upon which the construction for the Büchi automata builds. By outlining these concepts we advance our first goal of the research internship, which is to gain an understanding of the current research into this topic.

Secondly, we provide an alternate derivation of this coalgebraic representation using _game semantics_ #cite(<gradel2003automata>, supplement: "Chapter 10"). Game semantics is a framework for describing a system in terms of a two-player game between a _verifier_ and a _refuter_ who want to verify, respectively refute, a statement. We interpret a system of equations occuring in the coalgebraic representation as a game, to which we then apply established theorems from game semantics to derive the coincidence between the coalgebraic model and the traces of the Büchi automaton. Our game theoretic proof contrasts the algebraic proof given in @urabe2016coalgebraic. This formulation using game semantics might reveal connections to coalgebra automata which is based on game theoretic techniques @kupke2008coalgebraic.

The document is outlined as follows. In @sec:background we provide some background and relevant definitions for the rest of the report. In @chap:results we provide the coalgebraic representations of nondeterministic systems and Büchi automata from @hasuo2007generic and @urabe2016coalgebraic, respectively. In @sec:new we present our alternate derivation of the coincidence result given in the section before. Finally, in @sec:conclusion we summarize the results and suggest directions for future work.

#pagebreak()

= Background <sec:background>
// In this section we present the relevant background and definitions required for the rest of the report.

== Büchi Automata <sec:buchi>

Let us consider a very simple motivating example of a Büchi automaton, shown in @img:buchi.

#text(size: 9pt)[
  #align(center)[
    #figure(
      diagram(
        node((0, 0), [`idle`], name: <x0>, shape: circle, stroke: .5pt, width: 3.5em, extrude: (0, -5)),
        node((2, 0), [`running`], name: <x1>, shape: circle, stroke: .5pt, width: 3.5em),
        node((-.75, 0), [], name: <x-1>),
        edge(<x0>, <x1>, [`request`], "->", bend: +20deg),
        edge(<x1>, <x1>, [`process`], "->", bend: -130deg, loop-angle: 180deg),
        edge(<x1>, <x0>, [`return`], "->", bend: +20deg),
        edge(<x-1>, <x0>, "->"),
      ),
      caption: [Example of a Büchi automaton.],
    ) <img:buchi>
  ]
]

This system represents some machine that takes requests, processes them, and returns some result. One might want to verify that this machine does not get stuck. In terms of the system shown, this would mean that the machine always ends up in the `idle` state again.

This behavior can be modeled using a Büchi automaton. A Büchi automaton, namely, is an automaton which models infinite behavior, and accepts those infinite words for which there is a path through the automaton where the transitions are labeled by the letters of the word, an there is an accepting state that the path moves through infinitely many times. In this example, we make the `idle` state accepting, so the automaton accepts those words that always take the `return` transition again, and thus do not process indefinitely.

We can now give a formal definition of a Büchi automaton, and its _accepted language_:

#definition[
  A (nondeterministic) Büchi Automaton is a tuple $A=angle.l S, Sigma, delta, s_0, F angle.r$, with $S$ a finite set of states, $Sigma$ the finite alphabet, $s_0 in S$ the initial state, $delta : S times Sigma -> cal(P)(S)$ the transition function, $F subset.eq S$ the set of _final_ (or _accepting_) states.
]

A _run_ of a Büchi Automaton $A$ on an $omega$-word $w=sigma_0 sigma_1 dots in Sigma^omega$ is an infinite sequence of states $s_0,s_1,... in S^omega$, such that $s_0$ is the initial state and for every $n in omega$, $s_(n+1) in delta(s_n,sigma_n)$. A run is _accepting_ if it passes through an accepting state infinitely many times. Equivalently (because $F$ is finite), a run $rho=s_0,s_1,...$ is accepted if ${i | s_i in F}$ is an infinite set. A word $w$ is _accepted_ by a Büchi automaton $A$ if there is an acccepting run of $A$ on $w$. Finally, the _accepted language_ $L(A)$ of a Büchi automaton, is the set of words accepted by $A$, and $L(A)(s)$ is the set of words accepted by $A$ starting in state $s$.

Indeed we now see that the accepted language for the example automaton is $(mono("request") dot mono("process")^*dot mono("return"))^omega$, where $*$ indicates repeating some set of letters/transitions some finite number of times (including zero) and $omega$ indicates repeating indefinitely. That is, the machine gets a request, processes for at most some _finite_ number of transitions and then returns some result. It does not get stuck processing indefinitely.

== Parity Tree Automata <sec:tree>
Büchi automata are actually a specific instance of _parity tree automata_. In this section we introduce this more general automaton. Although we mainly discuss Büchi automata in the report, we mention parity tree automata because the coincidence results presented in @results:buchi also hold for parity tree automata, as discussed further in @results:buchi.

Instead of the acceptence criterion for Büchi automaton, we can use the parity acceptence condition. In this case, the states are not divided into accepting and non-accepting. Instead, every state has a priority, determined by $Omega: S -> omega$. A run $rho=s_0,s_1,dots$ of an automaton $A$ on a word $w$ is then accepting if the maximum priority that occurs infinitely often is even. I.e., $max{Omega(s) | s "occurs infinitely often in" rho}$ is even. The Büchi acceptence criterion is the special case where non-accepting states have parity $1$ and accepting states have parity $2$.

Secondly, instead of words we can have a tree automaton. In this case the alphabet $Sigma$ is _ranked_ and has an arity function function $|\_\_|:Sigma -> omega$ indicating the number of successors a letter has. Let $Tree_Sigma$ be the set of trees whose nodes are labeled with letters $sigma in Sigma$ and whose branching is consistent with the arity of the letters. For example, if $|sigma|=2$ for all $sigma in Sigma$, a tree $tau in Tree_Sigma$ is a binary tree with labels $sigma in Sigma$. If $|sigma|=1$ for all $sigma in Sigma$, $Tree_Sigma$ is just the set of infinite words over $Sigma$.

We can now define a parity tree automaton:

#definition[
  A (nondeterministic) Parity Tree Automaton is a tuple $A=angle.l S, Sigma, delta, s_0, Omega angle.r$, with $S$ a finite set of states, $Sigma$ a ranked alphabet with arity function $|\_\_|: Sigma -> omega$, $s_0 in S$ the initial state, $delta : S times Sigma -> cal(P)(S^*)$ the transition function where for each $sigma in Sigma$ if $|sigma|=n$ then $delta(s)(sigma)subset.eq S^n$, and $Omega: S -> omega$ assigns a parity to each state.

  A run $rho$ of the automaton $A$ on a tree $tau in Tree_Sigma$ is the tree $tau$ where the labels are replaced from letters $sigma in Sigma$ to states $s in S$ such that the root of the tree $rho_0=s_0$ is the initial state, and for a node in $tau$ with label $sigma in Sigma$ the associated node in $rho$ with label $s in S$ has children $s_1,dots,s_(|sigma|)$ such that $(s_1,dots,s_(|sigma|)) in delta(s)(sigma)$. A run is accepted if for every branch of the tree, the maximum priority that occurs infinitely is even. A tree $tau in Tree_Sigma$ is accepted by $A$ if there is an accepting run of $A$ on $tau$. The accepted language of $A$ is the set of accepted trees.
]



== Fixed Points
Crucial for the next section, @sec:modal about modal mu-calculus, is reasoning about _fixed points_ of _monotone_ functions. We briefly recall the important definitions and theorems.

#definition[
  A _complete lattice_ is a partially ordered set $angle.l L, <= angle.r$ such that every subset $M subset.eq L$ has a least upper bound $or.big M$ and greatest lower bound $and.big M$. Specifically, the whole set $L$ has a least and greatest element, which we denote $and.big L = bot$ and $or.big L = top$, respectively.
]

In this report we usually deal with the powerset of some set where subsets are ordered by inclusion. For a set $S$, $angle.l cal(P)(S), subset.eq angle.r$ is a complete lattice. For $U subset.eq cal(P)(S)$, $or.big U := union.big U$, and $and.big U := sect.big U$. The least and greatest elements are $emptyset$ and $S$, respectively. The following is known as the Knaster-Tarski Fixed Point Theorem #cite(<arnold2001rudiments>, supplement: "Theorem 1.2.8"):

#theorem()[
  Let $angle.l L, <= angle.r $ a complete lattice and $f:L->L$ monotone ($f(x) <= f(y)$ when $x<=y$). Then, the set of fixed points ${x in L|f(x)=x}$, is a complete lattice. Particularly, the function has a _least fixed point_ (lfp), denoted $lfp(f)$, and a _greatest fixed point_ (gfp), denoted $gfp(f)$.
] <th:knaster-tarski>

There is a useful way of constructing these least and greatest fixed points. This is done by repeated function application on $bot$ for the least fixed point, and $top$ for the greatest fixed point. Concretely, we define for a monotone $f:L->L$, for $alpha$ an ordinal, and $beta$ a limit ordinal:

$
  f^0 &:= bot \
  f^(alpha+1) &:= (f^alpha) \
  f^beta &:= or.big{f^alpha | alpha < beta}
$

This constructs an increasing chain
$ bot = f^0 <= f^1 <= f^2 <= ... $

which eventually stabilizes, giving the least fixed point, as stated by the following theorem:

#theorem()[
  There exists an ordinal $kappa$, such that $f^kappa=f^(kappa+1)$, which implies that $f^kappa$ is a fixed point of $f$. Furthermore, $f^kappa=lfp(f)$ is the least fixed point of $f$.
  The dual process, beginning from $top$ and moving downward, constructs the greatest fixed point of $f$.
] <th:knaster-tarski2>

== Modal $mu$-Calculus <sec:modal>
The modal $mu$-calculus is a powerful logic, used to verify properties of transition systems @gradel2003automata@arnold2001rudiments. We use it in @results:buchi to select the right accepting trees for the coalgebraic system. In this section we give a concrete definition of modal $mu$-calculus formulas and provide intuition on how to use the modal $mu$-calculus to verify certain properties. We verify these properties over _transition systems_, which we define first:

#definition[
  A transition system (TS) is a tuple $T=angle.l S, delta, italic("Prop"), lambda angle.r$ where $S$ is the set of states, $delta subset.eq S times S$ the transition relation (we sometimes write $s -> s'$ if $(s,s') in R$), $italic("Prop")$ the set of atomic propositions, and $lambda:italic("Prop")->cal(P)(S)$ interprets the atomic propositions.
]

A TS can be seen as a directed graph where the vertices are labeled by atomic propositions $cal(P)(Prop)$. Note that usually the modal $mu$-calculus is defined on _labeled_ transition systems, but to simplify things slightly, and because we only need unlabeled transition systems in the rest of the report we stick to transition systems.

Next we define the syntax of the modal $mu$-calculus:

#definition[
  A modal $mu$-calculus formula is defined by the grammar:
  $
    phi := P | Z | not phi | phi_1 and phi_2 | phi_1 or phi_2 | box phi | diamond phi | mu Z. phi | nu Z.phi
  $
  where $P in italic("Prop")$ is an atomic proposition and $Z in italic("Var")$ a _fixed point variable_.
] <def:modal>

Note that we could define the modal $mu$-calculus without the $or$, $diamond$, and $nu$ operators, and define these instead in terms of the other operators, but we include them in the definition for legibility.

#definition[
  For a modal $mu$-calculus formula $phi$, a transition system $T=angle.l S, delta, Prop, lambda angle.r$, and an assignment $V: italic("Var")->cal(P)(S)$ we define the semantics of the formula $||phi||_V^T subset.eq S$ as follows:
  $
    ||P||^T_V & := lambda(P)\
    ||not P||^T_V & := S backslash lambda(P)\
    ||Z||^T_V & := V(Z) \
    || phi_1 and phi_2 ||^T_V & := ||phi_1||^T_V sect ||phi_2||^T_V \
    || phi_1 or phi_2 ||^T_V & := ||phi_1||^T_V union ||phi_2||^T_V \
    || box phi ||^T_V &:= {s | forall t in S. "if" s-> t "then" t in ||phi||^T_V} \
    || diamond phi ||^T_V &:= {s | exists t in S. s-> t "and" t in ||phi||^T_V} \
    || mu Z.phi ||^T_V &:= italic("lfp")(lambda U. ||phi||^T_(V[Z |-> U]))\
    || nu Z.phi ||^T_V &:= italic("gfp")(lambda U. ||phi||^T_(V[Z |-> U]))
  $
  where $V[Z|->U]$ is the valuation $V$ except that $Z$ maps to $U$.

  We write $s scripts(tack.r.double)^(T)#h(-.1em) phi$ if $s in |phi|^T_V$ for an empty valuation $V$, or just $s tack.r.double phi$ if $T$ is clear.
]

Let us briefly look at some intuition behind these definitions. We have $s scripts(tack.double)^T p$ if in $T$ at state $s$ the propositional variable $p$ holds. Conversely,$s scripts(tack.double)^T#h(-.1em) not p$ holds if $p$ does not hold in $s$. The $diamond$ and $box$ operators look at states reachable from $s$. For example, $s scripts(tack.double)^T#h(-.1em) diamond p$ is true if there is some state $s'$ such that $s -> s'$ and $s' scripts(tack.double)^T p$. Analagously, $s scripts(tack.double)^T#h(-.1em) box p$ is true if $p$ is true in all succesor states from $s$. Less intuitive are the $mu$ and $nu$ operators. Concretely, they identify least and greatest fixed points on functions from states to states. More intuitively, they can be used to define looping properties on transition systems, where $mu$ can be used for finite looping, and $nu$ for infinite looping. This will hopefully become more clear when looking at some examples:

#figure(
  diagram({
    node((-0.5, 0), $emptyset$)
    node((0, 0), [$s_0$], name: <x0>, shape: circle, stroke: .5pt)
    node((1, -.5), [$s_1$], name: <x1>, shape: circle, stroke: .5pt)
    node((1.5, -.5), ${p}$)
    node((1, .5), $s_2$, name: <x2>, shape: circle, stroke: .5pt)
    node((1.5, .5), ${q}$)

    edge(<x0>, <x1>, "->")
    edge(<x1>, <x2>, "->")
    edge(<x0>, <x2>, "->", bend: +15deg)
    edge(<x2>, <x0>, "->", bend: +15deg)
  }),
  caption: [Example of a TS. The sets next to the states denote the atomic propositions that hold in that state.],
) <img:lts>

#let holds = $tack.r.double$

Consider the transition system given in @img:lts. We have $s_0 tack.r.double diamond p$, because there is a transition from $s_0$ to a state where $p$ holds, namely $s_0 -> s_1$, because $s_1 tack.r.double p$. We, however, do not have $s_0 holds box p$, because $s_0 -> s_2$ and $s_2 tack.r.double.not p$.

To observe that $mu$ is associated with finite looping, we look at the fact that $s_0 holds mu Z.q or box Z$. This means that all finite paths from $s_0$ either eventually reach a state with no outgoing transitions, or reach a state where $q$ is true. We can see in @img:lts that from $s_0$ every path reaches a state where $q$ is true in finitely many steps. To more formally show that this holds, we make use of the method of constructing least and greatest fixed points in @th:knaster-tarski2. The function we are calculating the lfp for is $f:= lambda U. ||q|| union ||box U||$. The first iteration yields $f^1=f(emptyset)={s_2}$, because $s_2 holds q$. Continuing, $f^2={s_1,s_2}$ and $f^3={s_0,s_1,s_2}=f^4$. So the lfp is the entire set of states $S$, and thus $s_0 holds mu Z. q or box Z$.

Next we look at $nu$, which can be used for infinite looping. We show that $s_0 holds nu Z. diamond Z$. This intuitively means that there exists an infinite path from $s_0$. Indeed, we observe there are multiple infinite paths starting from $s_0$. We confirm by computing the gfp: $f^1=f(S)=diamond S=S$. Dually, observe that the lfp of this formula is $f^1(emptyset)=emptyset$. So we do not have $s_0 holds mu Z. diamond Z$. This confirms the intuition that $mu$ is for finite looping: there has to be some end point of the loop.


=== System of Equations

Next we introduce systems of equations with alternating fixed points. We demonstrate the system using only two equations for brevity and because they are the only ones needed in the rest of the report. For more detail into this specific topic see @arnold2001rudiments@urabe2016coalgebraic.

#definition[
  Let $L_1,L_2$ be complete lattices. An _equational system_ is a system of two equations

  $
    u_1 =_eta_1 f_1(u_1,u_2) #h(3em) u_2 =_eta_2 f_2(u_1,u_2)
  $
  where $u_1,u_2$ are variables, $eta_1,eta_2 in {mu,nu}$, and $f_i: L_1 times L_2 -> L_i$ are monotone functions. The solution to the system is defined by the following set of steps:

  The intermediate solution $l^((1))_1 := eta_1 u_1. f_1(u_1,u_2)$, where we take the lfp if $eta_1=mu$ and gfp if $eta_1=nu$. Note that $l^((1))_1:L_2 -> L_1$.

  The solution to the second equation is then given by $l^(sol):= eta_2 u_2. f_2(l^((1))_1(u_2), u_2)$, where again we take the lfp if $eta_2=mu$, and gfp if $eta_2=nu$. The solution to the first equation is then $l^sol_1 = l^((1))_1(l^sol_2)$.
] <def:eq>

== Parity Games
Next we introduce parity games and show how they provide both an intuitive and formal semantics for modal $mu$-calculus formulas. We use these semantics to prove the coincidence results in @sec:new.

A parity game is a two player game between $V$ (verifier) and $R$ (refuter), who want to verify, respectively refute, a statement. In our case, this statement is $s scripts(tack.double)^T#h(-.1em) phi$, i.e. that a modal $mu$-calculus formula holds in a state $s$ in LTS $T$. So $V$ wants to show $s scripts(tack.double)^T #h(-.1em)phi$ and $R$ wants to show $s scripts(tack.double.not)^T#h(-.1em) phi$. The game consists of states and transitions between these states. Every state 'belongs' to either $V$ or $R$, which determines which player picks the next transition and thus the next state. A play of the game is then a (possibly infinite) sequence of states, and is won by either $V$ or $R$. Concretely we define:

#definition()[
  A _parity game_ is a tuple $((S_V,S_R),E,Omega)$, where $S=S_V union.sq S_R$ is the set of states, partitioned between player $V$ ($S_V$) and player $R$ ($S_R$) who choose transitions from their repsective states, $E subset.eq S times S$ are transitions between the states, and $Omega:S->omega$ is the parity function, which determines the winner for infinite plays.

  A play of the game is a (possibly infinite) sequence of states $s_1,s_2, dots$ such that $(s_i,s_(i+1)) in E$. A finite play $s_1,s_2,dots,s_n$ is won by $V$ if $s_n in S_R$ and there is no $s_(n+1)$ such that $(s_n,s_(n+1)) in E$, i.e. player $R$ has no moves. Analagously, $R$ wins if player $V$ gets stuck. An infinite play $pi=s_1,s_2,dots$ is won by $V$ if $max{Omega(s) | s "occurs infinitely often in" pi}$ is even, and won by $R$ if it is odd.
]

Next, we introduce the parity game for the modal $mu$-calculus. Consider the formula $phi=phi_1 or phi_2$. $V$ wants to verify $s scripts(tack.double)^T#h(-.1em) phi$, and to do so it suffices to show for either $phi_i$ that $s scripts(tack.double)^T#h(-.1em) phi_i$. Analagously for the formula $phi=phi_1 and phi_2$, $R$ can 'pick' the $phi_i$ such that $s scripts(tack.double.not)^T#h(-.1em) phi_i$, because if either $phi_1$ or $phi_2$ does not hold, $phi$ does not hold. This same duality is seen in $diamond phi$ and $box phi$ where for $diamond$ $V$ can show there is a transition for which $phi$ holds, and for $box phi$, $R$ can pick a transition such that $phi$ does not hold. This way the game arises between $V$ and $R$ to determine whether $s scripts(tack.double)^T#h(-.1em) phi_i$:


#definition([Parity Game for Modal mu-Calculus@gradel2003automata])[
  For a transition system $T=(S,delta,Prop,lambda)$ and a modal $mu$-calculus formula $phi$, we define the game $cal(G)(phi,T)=((S_V,S_R),E,Omega)$ where:
  - #[The states of the game $S_V union.sq S_R= {phi' | phi' " is a subformula of " phi} times S$ are pairs of a subformula of $phi$ and a state in the TS. The subformula determines to which player the state belongs to. For a subformula $psi$ and a state $s$ of the TS:
      - #[$(psi,s) in S_V$ if
          - $psi= psi_1 or psi_2$
          - $psi= diamond psi'$
          - $psi= eta Z. psi'$ for $eta in {mu,nu}$
          - $psi=Z$ for $Z$ a fixed point variable
          - $psi = p$ for $p$ a propositional variable with $s in.not lambda(p)$.
          - $psi = not p$ for $p$ a propositional variable with $s in lambda(p)$.
        ]
      - #[$(psi,s) in S_R$, if
          - $psi=psi_1 and psi_2$
          - $psi = box psi'$
          - $psi = p$ for $p$ a propositional variable with $s in lambda(p)$.
          - $psi = not p$ for $p$ a propositional variable with $s in.not lambda(p)$.
        ]
    ]
  - Edges $E$:
    - $(psi_1 or psi_2,s)->(psi_1,s)$ and $(psi_1 or psi_2,s)->(psi_2,s)$
    - $(psi_1 and psi_2,s)->(psi_1,s)$ and $(psi_1 and psi_2,s)->(psi_2,s)$
    - $(diamond psi, s)->(psi,s')$ for any $s'$ such that $s -> s'$ in $T$.
    - $(box psi, s)->(psi,s')$ for any $s'$ such that $s -> s'$ in $T$.
    - $(eta Z. psi, s)-> (psi, s)$ and $(Z,s)->(psi,s)$ for $eta in {mu,nu}$
  - The priority function $Omega$ depends on the _alternation depth_ $alpha(psi)$ of the subformula $psi$, which is defined as follows:
    - $alpha(p)=alpha(not p)=0$ for $p$ a propositional variable
    - $alpha(psi_1 and psi_2)=alpha(psi_1 or psi_2)=max{alpha(psi_1),alpha(psi_2)}$
    - $alpha(diamond psi)=alpha(box psi)=alpha(psi)$
    - $alpha(mu Z.psi)=max({1,alpha(psi)} union {alpha(nu Z'.psi') +1 | nu Z'. psi' "is a subformula of" psi "and" Z "occurs free in " psi'} )$
    - $alpha(nu Z.psi)=max({1,alpha(psi)} union {alpha(mu Z'.psi') +1 | mu Z'. psi' "is a subformula of" psi "and" Z "occurs free in " psi'} )$
    Intuitively, the alternation depth of a formula is the maximum number of alternating $mu slash nu$ operators, where we only count those alternations where the free variable actually occurs freely in the subformula, meaning the fixed point operators are actually interdependent. $Omega$ is then:
    - $Omega((mu Z.psi,s))= $ the smallest odd number greater or equal than $alpha(psi)-1$
    - $Omega((nu Z.psi,s))= $ the smallest even number greater or equal than $alpha(psi)-1$
    - $Omega((psi,s))=0$ iff $psi$ is not a $mu$ or $nu$ formula.
] <def:paritygame>

Whereas the intuition for operators like $or,and,box,diamond$ is quite straightforward, for the $mu slash nu$ operators it is less so. Briefly put, it follows from what was explained in @sec:modal that $mu$ incites finite looping, and $nu$ infinite looping. It can be seen from the definition for $Omega$ using the alternation depth, that outer $mu slash nu$ operators have higher priority than inner ones, and $mu$ is always even and $nu$ odd. Thus the highest priority occuring infinitely often in an infinite play indicates the outermost fixed point operator that is visited infinitely often. Thus, if this is even, we have an infinite loop through a $nu$ operator, which satisfies the formula. For a $mu$ operator, however, an infinite loop is undesired, and thus if the outermost fixed point operator which is visited infinitely often is $mu$, $R$ has refuted the formula.

Now, to use this game to give alternative semantics for the modal $mu$-calculus we need that $s scripts(tack.double)^T#h(-.1em) phi$ if and only if $V$ can verify this in the game $cal(G)(phi,T)$ by winning the game, and $R$ can not win. We say that $V$ has a winning strategy: $V$ can always play (i.e. take the right transition if it is their turn) such that regardless of how $R$ plays, $V$ wins the play. We then have the crucial theorem (for the proof see #cite(<gradel2003automata>,supplement: "Theorem 10.18" )) for our derivation of the concidence results in @sec:new:

#theorem()[
  For a transition system $T=angle.l S, delta, Prop, lambda angle.r$, a state $s in S$, and a modal $mu$-calculus formula $phi$, we have:
  $
    s scripts(tack.double.r)^T phi <=> "V has a winning strategy in" cal(G)(phi,T) "starting in state" (phi,s)
  $
] <th:game>



= Coalgebraic Representation of Büchi Automata <chap:results>
== Finite Behavior of Nondeterministic Automata <sec:nd>
In this section we present a coalgebraic representation of nondeterministic systems. The next section for Büchi automata builds upon this construction.

=== Deterministic Automata <sec:d>

First we consider a deterministic finite automaton, $angle.l S, Sigma, delta, o angle.r $ with $S$ the states, $Sigma$ the alphabet, $delta: S times Sigma -> S$ the transition function, and $o: S -> 2$ with $2={0,1}$, the output function determining if a state is final. We do not consider an initial state here because we just want to obtain the accepted words for each state. Such an automaton can be represented by a coalgebra $c: S -> 2 times S^Sigma$ for the functor $F S=2 times S^Sigma$. This is a very useful construction because a final coalgebra for this functor is carried by $2^Sigma^*$, and the unique coalgebra homomorphism $beh$ to this final coalgebra captures exactly the language accepted by a state @rutten2000universal. This is shown in the commuting diagram:

$
  #diagram(
  // spacing: 2cm,
  {
    node((0, 0), $2 times S^Sigma$, name: <FX>)
    node((0, 1), $S$, name: <X>)
    node((1, 0), $2times (2^Sigma^*)^Sigma$, name: <FZ>)
    node((1, 1), $2^Sigma^*$, name: <Z>)

    edge(<X>, <FX>, $angle.l o,delta angle.r$, "->", label-side: left)
    edge(<Z>, <FZ>, $angle.l e,d angle.r$, "->", label-side: right)
    edge(<X>, <Z>, $beh$, label-side: right, "-->")
    edge(<FX>, <FZ>, $id times beh^Sigma$, "-->")
  },
)
$

Here $e: 2^Sigma^*-> 2$ is given by $e(L) = L(epsilon)$, i.e., $e(L) = 1$ iff L contains the empty word. And $d: 2^Sigma^* -> (2^Sigma^*)^Sigma$ is the language derivative, given by $d(L)(sigma)=L_sigma$ where $L_(sigma)(w)=L(sigma w)$, so $w in d(L)(sigma)=L_sigma$ iff $sigma w in L$.

Working out the paths through the diagram we obtain that
- $beh(s)(epsilon)=o(s)$, and
- $beh(s)(sigma w)=beh(delta(s)(sigma))(w)$,

for $s in S$, $sigma in Sigma$, $w in Sigma^*$. So $beh(s)$ contains the empty word iff $s$ is a final state, and accepts $sigma w$ iff $delta(s)(sigma)$ accepts $w$. Which is precisely the language accepted by state $x$ in the deterministic finite automaton!

=== Nondeterministic Automata <sec:finite>

Unfortunately, extending this approach to nondeterministic automata is not possible, as we will illustrate by the following automaton, which we will use as a running example:

// #align(center)[
#figure(
  diagram(
    spacing: 2em,
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
  caption: [Example of a nondeterministic automaton.],
) <img:nd>
// ]

The automaton given in @img:nd is nondeterministic because in $s_0$ there are two transitions for $a$. Intuitively, the finite words accepted by the automaton from state $s_0$ should be
$ tr(s_0) = {a, a b, a b b, ...} union {a, a c, a c c, ...}. $

This transitions system might be modeled by a coalgebra $c: S -> 2 times cal(P)(Sigma times S)$, i.e., for every state whether it is final, and a set of pairs $(sigma,s) in Sigma times S$ denoting a transition by taking letter $sigma$ and transitioning to state $s$. The problem is that this functor $F S = 2 times cal(P)(Sigma times S)$ does not have a final coalgebra, as Lambek's lemma implies that such a final coalgebra structure $z: Z -> 2 times cal(P)(Sigma times Z)$ for some carrier $Z$, would have to be an isomorphism @awodey2010category. But an isomorphism $Z tilde.equiv 2 times cal(P)(Sigma times Z)$ would imply a bijection between $Z$ and $cal(P)(Z)$, which cannot exist.

The solution, as given by Hasuo et al. @hasuo2007generic, is to work in the Kleisli category for the monad $cal(P)$. Recall that a map $f: X -> Y$ in the Kleisli category is a map $f: X -> cal(P)(Y)$ in *Sets*. Briefly put, this will solve our problem because we can have a final coalgebra $z: Z -> F Z$ that is a map $z: Z -> cal(P)(F Z)$ in *Sets*. Next, we will review the definition of the Kleisli category and define the appropriate functor, enabling us to construct the desired final coalgebra that characterizes the accepting finite words.

The powerset monad $cal(P)$ is defined by the unit $eta_X : X -> cal(P)(X)$ which sends an element of $X$ to the singleton set, $eta_X (x)={x}$ for $x in X$, and the multiplication $mu_X: cal(P)(cal(P)(X)) -> cal(P)(X)$ which takes the union of the sets, i.e. $mu_X (A) = union.big_(a in A) a$. For a function $f: X -> Y$ we get $cal(P)(f): cal(P)(X) -> cal(P)(Y)$ by $cal(P)(f)(A)= {f(a) | a in A}$. The Kleisli category for this monad is defined as follows:
- *objects*: the same as for *Sets*, sets
- *morphisms*: #[a morphism $f$ from $X$ to $Y$ in $Klp$ is a map $f:X-> cal(P)(Y)$ in *Sets*.

The identity morphism $id_X:X -> X$ is defined by $id_X(x)={x}$, which is indeed a mapping from $X$ to $cal(P)(X)$ in *Sets*. Composition $(g compose f)$ in $Klp$ for morphisms $f: X -> Y$ and $g: Y -> Z$ in $Klp$ (so $f: X-> cal(P)(Y)$ and $g: Y -> cal(P)(Z)$ in *Sets*) is defined as $(mu_Z compose cal(P)(g) compose f)$ in *Sets*. Again we see that that this definition is of the right type as $(mu_Z compose cal(P)(g) compose f): X -> cal(P)(Z)$ in *Sets*, so $(g compose f): X -> Z$ in $Klp$.
]

Next, we construct our functor in $Klp$, which we call the lifting of $F$ in $Klp$, and denote $overline(F)$. The key here is that because we are working in the Kleisli category, if we use the functor $overline(F) S = Sigma times S$, the coalgebra map $c: S -> Sigma times S$, will be a map $c: S -> cal(P)(Sigma times S)$ in *Sets*, which models nondeterministic transitions. In the previous section we used the functor $F S -> 2 times S ^ Sigma$ where $o: S -> 2$ denoted whether the state was final. Combining this with the functor $overline(F) S = Sigma times S$ in the Kleisli category we would get the functor $overline(F) S = 2 times Sigma times S$ and the coalgebra $c: S -> 2times Sigma times S$ which is $c: S -> cal(P)(2 times Sigma times S)$ in *Sets*, which would mean that every transition can be final or not, which is not what we want. For this reason we use the functor $overline(F) S = 1 + Sigma times S$ such that the coalgebra $c: S -> 1 + Sigma times S$ is the map $c: S -> cal(P)(1 + Sigma times S)$ where $s in S$ is final iff $* in c(s)$ (note that we use $1={*}$).

This works easily on objects, $overline(F)X=F X$, because in the Kleisli category, the objects are the same. But for morphisms we have to do a little bit more work. Observe that because a map $f:X-> Y$ in $Klp$ is a map $f: X->cal(P)(X)$ in *Sets*, applying the functor $F$ on the map itself would yield $F f: F X -> F cal(P) (Y)$. So what we need is a natural transformation $lambda: F cal(P) => cal(P) F$ (this is a distributive law, for more details see for example @hasuo2007generic) such that $1+Sigma times (cal(P)(S)) ->^lambda cal(P)(1+Sigma times S)$. We define this as $* arrow.r.bar {*}$, and $(sigma,U)={(sigma,s)|s in U}$ for $sigma in Sigma$ and $U subset.eq S$. We see that this definition makes sense if we observe that if taking transition $sigma$ from state $s$ takes you to ${x,y,z}$, i.e. $(sigma,{x,y,z}) in c(s)$, or ${x,y,z} in delta(s)(sigma)$, you can also see this as a set of transitions ${(sigma,x),(sigma,y),(sigma,z)}$.

Finally, the main theorem from @hasuo2007generic (Theorem 3.3), and the last ingredient to make the construction work, is that the initial algebra for the functor $F$ in *Sets* gives us the final coalgebra for the lifted functor $overline(F)$ in $Klp$. Specifically, for this functor $F S= 1 + Sigma times S$ and its lifting as described above, the initial $F$-algebra $alpha: F A -> A$ in *Sets* yields a final $overline(F)$-coalgebra in $cal("Kl")(cal(P))$ by:

$ (eta_(F A) alpha)^(-1) = eta_(F A) alpha^(-1) : A -> overline(F)A italic("in") cal("Kl")(cal(P)) $

In fact, this result holds more generally: for the lifting monad $cal(L)$, the subdistribution monad $cal(D)$, and any shapely functor $F$, see @hasuo2007generic for more details.

The initial $F$-algebra for our functor $F S = 1 + Sigma times S$ in *Sets* is $[sans("nil"),sans("cons")]: 1 + Sigma times Sigma^* -> Sigma^*$. So we get the commuting diagram

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

Following the paths within the diagram we obtain that

$
  epsilon in tr(s) <==> * in c(s) <==> "state" s "is accepting"\
  sigma w in tr(s) <==> exists t. (s ->^sigma t and w in tr(t)).
$ <eq:finite>

Explained in words, a state accepts the empty word iff the state is accepting, and it accepts $sigma w$ for $sigma in Sigma$ and $w in Sigma^*$ iff it can transition with $sigma$ to a state which accepts $w$. Which is exactly the desired words!

// _should be explained more_

// #definition("LTL")[
// 	A (nondeterministic) Labeled Transition System (LTL) is a tuple $angle.l X,Sigma,delta angle.r$, consisting of a set of states $X$, an alphabet $Sigma$, a transition system $delta: X times Sigma -> cal(P)(X) union {checkmark}$. Where checkmark is explicit termination.
// ]

=== Possibly Infinite Behavior <sec:infinite>
As a step towards infinite words in Büchi automata let us consider infinite words in @img:nd. We can slightly alter our previous construction to additionally obtain infinite words through this system @jacobs2004trace@hasuo2007generic. Concretely, the infinite words for the system in @img:nd for $x_0$ are $a b^omega$ and $a c^omega$.

The intuition for this new construction is as follows. In the previous section we constructed the final coalgebra for the lifted functor $overline(F)$ using the initial $F$-algebra in *Sets*. In the example of the LTS with termination the initial algebra was carried by $Sigma^*$. The final coalgebra in *Sets* for $F$ is carried by $Sigma^infinity$ (where the $infinity$ operators means some finite number of times or indefinitely so $Sigma^infinity = Sigma^* union Sigma^omega$) the set of finite and infinite words. So if we use this final coalgebra instead of the initial algebra, do we obtain both the finite and infinite words?

Consider again the monad $cal(P)$, our functor $F$ (this too holds more generally, see @hasuo2007generic@jacobs2004trace), and its lifting in the Kleisli category $overline(F)$. For a final coalgebra $xi: Z-> F Z$, the coalgebra

$ eta_(F Z) compose xi : Z -> overline(F) Z italic("in") Klp $

is _weakly final_. That means, for any coalgebra $c: S -> overline(F)S$, there is a morphism $tr:S -> Z$ in $Klp$ such that the following diagram commutes

$
  #diagram(
    // spacing: 2cm,
    {
      node((0, 1), $S$, name: <X>)
      node((0, 0), $overline(F) S$, name: <FX>)
      node((1, 1), $Z$, name: <Z>)
      node((1, 0), $overline(F) Z$, name: <FZ>)
      edge(<X>, <FX>, $c$, "->", label-side: left)
      edge(<Z>, <FZ>, $tilde.equiv$, "-", label-side: left, stroke: 0pt)
      edge(<Z>, <FZ>, $eta_(F Z) compose xi$, "->", label-side: right)
      edge(<X>, <Z>, $text(tr)$, "~>", label-side: right)
      edge(<FX>, <FZ>, $overline(F)(text(tr))$, "~>")
      node((2, .5), $italic("in") cal("Kl")(cal(P)),$)
    },
  )
$ <eq:possiblyinfinite>

but this morphism is not necessarily unique. However, there is a canonical choice $tr^infinity$ among these morphisms, namely the one which is maximal with respect to inclusion. We call this function $tr^infinity : S -> cal(P)(Z)$ (in *Sets*) the _possibly-infinite_ behavior for $c$.

Indeed, if we consider our running example @img:nd with termination,
// $
//   #diagram(
//     // spacing: 2cm,
//     {
//       node((0, 1), $X$, name: <X>)
//       node((0, 0), $1 + Sigma times X$, name: <FX>)
//       node((1, 1), $Sigma^infinity$, name: <A>)
//       node((1, 0), [$1 + Sigma times Sigma^infinity$], name: <FA>)
//       edge(<X>, <FX>, $c$, "->", label-side: left)
//       edge(<A>, <FA>, $tilde.equiv$, "-", label-side: left, stroke: 0pt)
//       edge(<A>, <FA>, $J xi$, "->", label-side: right)
//       edge(<X>, <A>, $text(tr)^infinity_c$, "~>", label-side: right)
//       edge(<FX>, <FA>, $1 + Sigma times tr^infinity_c$, "~>")
//       node((2, .5), $italic("in") cal("Kl")(cal(P)).$)
//     },
//   )
// $
$xi: Sigma^infinity -> 1 + Sigma times Sigma^infinity$ is the final $F$-coalgebra, defined by $xi(epsilon)& =* in 1$ and $xi(sigma w)&= (sigma,w)$. Instantiating the diagram in @eq:possiblyinfinite, we obtain
$
  epsilon in tr^infinity (s) <==> * in c(s) <==> "state" s "is accepting" \
  sigma w in tr^infinity (s) <==> exists t. (s ->^sigma t and w in tr^infinity (t)).
$ <eq:infinite>

Which is the same as in @eq:finite. However, because the domain is $Sigma^infinity$, we obtain different words when we take the maximal function satisfying these equations. Namely the infinite words, in addition to the finite ones! For the system in @img:nd we get the same words as before, but additionally ${a b^infinity, a c^infinity} subset.eq tr^infinity_c (s_0)$. Interestingly, taking the minimum morphism we again obtain just the finite words @hasuo2007generic@jacobs2004trace.

== Coalgebraic Representation of Büchi Automata <results:buchi>
We can apply the previous framework for possibly infinite words to our initial example for a Büchi automaton, in @img:buchi. This would yield all infinite words through the automaton, so also for example $mono("request") dot mono("process")^omega$), it does not take into account accepting states, only for ending finite words. How do we eliminate those words that process indefinitely? That is, only accept those words under the Büchi acceptance criterion of passing through an accepting state infinitely many times.

A way of solving this is given by @urabe2016coalgebraic. In short, the main idea of this paper is to divide the states into accepting and non-accepting states. Then, applying the previous construction using the final $F$-coalgebra in *Sets* we obtain two separate commuting diagrams for these disjoint sets of states. And finally, using greatest and least fixed points we can precisely pick exactly the accepting words for the Büchi automaton.

We first give the commuting diagrams which govern the behavior mappings. We are now considering Büchi automata, so the functor we consider is $F S = Sigma times S$, the final coalgebra for this functor is $d: Sigma^omega -> Sigma times Sigma^omega$, defined by $d(sigma dot w) = (sigma,w)$, and the monad is still $cal(P)$. The lifting $overline(F)$ is effectively the same, just without a case for $*in 1$. We now consider the state space as a disjoint union $S=S_1 union S_2$ of non-accepting and accepting states, respectively. This gives rise to two separate coalgebras $c_i: S_i -> overline(F)X$, defined by the restriction $c compose kappa_i : S_i -> overline(F)X $ along the coprojection $kappa_i : S_i arrow.r.hook S$ for $i in {1,2}$. We then get the two commuting diagrams:

$
  #diagram(
    spacing: 1.1cm,
    {
      node((0, 0), [$Sigma times S$], name: <fx1>)
      node((0, 1), [$S_1$], name: <x1>)
      node((1, 1), [$Sigma^omega$], name: <z1>)
      node((1, 0), [$Sigma times Sigma^omega$], name: <fz1>)
      edge(<x1>, <fx1>, $c_1$, "->", left)
      edge(<x1>, <z1>, $tr_1$, "~>", right)
      edge(<fx1>, <fz1>, $Sigma times [tr_1,tr_2]$, "~>")
      edge(<z1>, <fz1>, $eta_(Sigma^omega) compose  d$, right,"->")
      edge(<z1>, <fz1>, $tilde.equiv$, "-", left, stroke: 0pt)

      node((2, 0), [$Sigma times S$], name: <fx2>)
      node((2, 1), [$S_2$], name: <x2>)
      node((3, 1), [$Sigma^omega$], name: <z2>)
      node((3, 0), [$Sigma times Sigma^omega$], name: <fz2>)
      edge(<x2>, <fx2>, $c_2$, "->", left)
      edge(<x2>, <z2>, $tr_2$, "~>", right)
      edge(<fx2>, <fz2>, $Sigma times [tr_1,tr_2]$, "~>")
      edge(<z2>, <fz2>, $eta_(Sigma^omega) d$, "->")
      edge(<z2>, <fz2>, $tilde.equiv$, "-", left, stroke: 0pt)

      node((0.5,0.5), [$=_mu$])
      node((2.5,0.5), [$=_nu$])

      node((3.75, .5), $italic("in") cal("Kl")(cal(P)).$)
    },
  )
$ <eq:diagram>

// What the $=_mu$ and $=_nu$ in the center of the diagrams mean we will see later.
Where $=_mu$ and $=_nu$ mean that we take the least behavior mapping in the left diagram to obtain $beh_1$, and the greatest behavior mapping in the right diagram to obtain $beh_2$. More concretely, $beh_1: S_1 -> cal(P)(Sigma^omega)$ and $beh_2: S_2 -> cal(P)(Sigma^omega)$, are the solutions to the following system of equations:

// Spelling out the paths within the diagram we obtain that our behavior mapping $tr_1: X_1 -> cal(P)(Sigma^omega)$, $tr_2: X_2 -> cal(P)(Sigma^omega)$ must conform to the following equations.

$
  u_1 &=_mu (eta_(Sigma^omega) compose d)^(-1) dot.circle overline(F)[u_1,u_2] dot.circle c_1 \
  u_2 &=_nu (eta_(Sigma^omega)compose d)^(-1) dot.circle overline(F)[u_1,u_2] dot.circle c_2
$ <eq:traces>

At this point we note that this construction works for the more general parity tree automata from @sec:tree. A parity tree automata can be modeled by the lifted functor of the functor $F S = union.sq_(sigma in Sigma) S^(|sigma|)$ (where $union.sq$ is the coproduct). The final coalgebra of $F$ in *Sets* is $d: Tree_Sigma -> union.sq_(sigma in Sigma) Tree_Sigma^(|sigma|)$ where $d((sigma,(tau_1,dots,tau_(|sigma|))))=(tau_1,dots,tau_(|sigma|))$. We model the different parities by splitting the states into $S=S_1 union dots union S_n$ where for every $S_i$ we have $s in S_i -> Omega(s)=i$ and we have a seperate commuting diagram like in @eq:diagram for every parity, where the $mu$ and $nu$ alternate. We then get the following equations for a parity tree automaton with $n$ parities:

$
  u_1 &=_mu (eta_(Tree_Sigma) compose d)^(-1) dot.circle overline(F)[u_1,dots,u_n] dot.circle c_1 \
  u_2 &=_nu (eta_(Tree_Sigma)compose d)^(-1) dot.circle overline(F)[u_1,dots, u_n] dot.circle c_2\
  & dots.v \
  u_n &=_(eta_n) (eta_(Tree_Sigma)compose d)^(-1) dot.circle overline(F)[u_1,dots, u_n] dot.circle c_n\
$ <eq:traces-parity>

where $eta_i=mu$ if $i$ is odd and $eta_i=nu$ if $i$ is even. We confirm here that the Büchi case is a specific instance of the parity acceptence criterion by letting $n=2$ and just having one $mu$ and one $nu$ equation. Before continuing, we rewrite the equations to be more clear and usable:

#lemma()[
  The traces in @eq:traces-parity coincide with:

  $
    u_1 =^mu diamond_delta ([u_1,dots, u_n]) harpoon.tr S_1, #h(1em) dots,  #h(1em) u_n =^(eta_n) diamond_delta ([u_1,dots,u_n]) harpoon.tr S_n
  $

  Where $diamond_delta: (cal(P)(Tree_Sigma))^(S)->(cal(P)(Tree_Sigma))^(S)$ is given by
  $
    diamond_delta (beh)(s) = { (sigma,(tau_1,dots,tau_(|sigma|))) | (s^'_1,dots,s^'_(|sigma|)) in delta(s)(sigma), tau_i in beh(s^'_i)}.
  $ <eq:diamond>
] <lemma:0>

The proof can be found in @appendix:lemma:0.

By taking exactly those behavior mappings which are the solution to this system of equation, we take exactly those words that the parity tree automaton accepts:

#lemma([#cite(<urabe2016coalgebraic>, supplement: "Lemma 4.5")])[
  Let $A=(S, Sigma, delta, s_0, Sigma)$ be a parity tree automaton, where we let $S=S_1 union dots union S_n$ the disjunct union of states with parity $1, dots, n$, respectively. Let $l^sol_i$ be the solutions to the following equational system, where the variables $u_1,dots,u_n$ range over $(cal(P)(Tree_Sigma))^(S_i)$

  $
    u_1 =^mu diamond_delta ([u_1,dots, u_n]) harpoon.tr S_1, #h(1em) dots,  #h(1em) u_n =^(eta_n) diamond_delta ([u_1,dots,u_n]) harpoon.tr S_n
  $ <eq:traces2>

  Where $diamond_delta: (cal(P)(Tree_Sigma))^(S)->(cal(P)(Tree_Sigma))^(S)$ is given by
  $
    diamond_delta (beh)(s) = { (sigma,(tau_1,dots,tau_(|sigma|))) | sigma in Sigma, (s^'_1,dots,s^'_(|sigma|)) in delta(s)(sigma), tau_i in beh(s^'_i)}.
  $
  Then the solutions $l^sol_i : S_i -> cal(P)(Tree_Sigma)$ map $S_i$ to the accepted language from that state, that is, $l^sol_i (s) = L(A)(s)$ for $s in S_i$.
] <lemma:4.5>

We provide a brief intuition here, utilizing what was observed in @sec:modal. Namely, that $mu$ is associated with finite looping, and $nu$ with infinite. So the even equation makes sure the run passes through even parities infinitely many times. Note that it can still move states with odd parities, but it has to move through those with even parities infinitely many times. Those odd equations make sure there is a finite loop back to an even equation.

Regardless of this intuition, the proof of this lemma given in @urabe2016coalgebraic is rather complex. In the next section we provide our proof using game semantics, which we believe is a lot more comprehensive.

Combining @lemma:0 and @lemma:4.5 we obtain the coincidence result:

#theorem([#cite(<urabe2016coalgebraic>, supplement: "Theorem 4.6")])[
  Let $A=(S, Sigma, delta, s_0, Sigma)$ be a parity tree automaton. Then the behavior mappings $tr_1,dots,tr_n$, which are the solution to the system of equations in @eq:traces2 coincide with the accepted language of $A$: $beh(s_0)=[tr_1,dots,tr_n](s_0) = L(A)$.
] <th>

= Derivation of Coincidence Using Game Semantics <sec:new>
In this section we provide our derivation of the coincidence result @lemma:4.5. At the core of the derivation is @th:game, which relates a modal mu calculus formula on a transition system and a parity game. We can apply @th:game to derive the coincidence result with the following strategy:

1. Derive from a formula $phi$ from the system of equations in @eq:traces2 a closed modal mu-calculus formula $overline(phi)$ and define a transition system $T_A$ from the parity tree automaton $A$ such that the $overline(phi)$ holds on a state in $T_A$ if and only if $phi$ holds in a related state on $A$.
2. Apply @th:game to conclude that $overline(phi)$ holds in a state $s$ if and only if there exists a winning strategy for $V$ on $cal(G)(T_A,overline(phi))$ from state $s$.
3. Prove that there exists a winning strategy for $V$ from state $(s,w)$ in $cal(G)(T_A,overline(phi))$ if and only if $w in L(A)(s)$

Unfortunately, we have not been able to prove step 3 for the parity acceptance criterion, just for the Büchi case. We do solve steps 1 and 2 for the general case, and then provide the proof of step 3 for the Büchi automaton on trees. // We discuss this further below and in @sec:conclusion.

So the first step is defining the transition system from the parity tree automaton.

#definition[
  Let $A=(S, Sigma, delta, s_0, Sigma)$ be a parity tree automaton, where we let $S=S_1 union dots union S_n$ the disjunct union of states with parity $1, dots, n$, respectively, $Sigma$ is the alphabet, and $delta: S times Sigma -> cal(P)(S^*)$ the transition function. We define a Transition System (TS) over the set of propositional variables ${p_1,dots,p_n}$ for this automaton, denoted as $T_A$, as follows:
  - States are either $(s,tau)$ for $s in S$ and $tau in Tree$ or $((s_1,dots,s_(|sigma|)), (tau_1,...,tau_(|sigma|)))$ for $s_i in S$, $tau_i in Tree$
  - Transitions from state $(s,tau)$, for $s,s'in S, sigma in Sigma, tau in Tree_Sigma$:
  $
    (s,(sigma,(tau_1,dots,tau_(|sigma|)))) -> ((s_1^',dots, s_(|sigma|)^'), (tau_1,dots,tau_(|sigma|))) "for all" (s_(1)^',dots,s_(|sigma|)^') in delta(s)(sigma)
  $ <eq:transition1>
  - Transitions from state $((s_1,dots, s_(|sigma|)), (tau_1,dots,tau_(|sigma|)))$ for $s_i in S, sigma in Sigma, tau_i in Tree_Sigma$:
  $
    ((s_1,dots, s_(|sigma|)), (tau_1,dots,tau_(|sigma|))) -> (s_i, tau_i) "for all" i in {1,...,|sigma|}
  $ <eq:transition2>
  - Labeling function given by $lambda((s,tau))={p_i}$ iff $s in S_i$, i.e., the propositional variables denote for what $i$, we have $s in S_i$.
]

By defining the states of the transition system as state-tree pairs on the parity tree automaton, we ensure that step 3 of the strategy succeeds: this setup allows for a clear correspondence between an infinite play in the parity game and an accepting run through the parity tree automaton.

Next, we derive a closed modal mu-calculus formula from the system of equations. Deriving the solution from the system of equations, as explained in @def:eq, obtains a closed formula. For example, for the Büchi case (two parities) the closed formula for $beh_1: S_1 -> cal(P)(Tree_Sigma)$ from @eq:traces2 is $beh_1=nu u_2. diamond_delta [mu u_1. [u_1,u_2] arrow.t S_1, u_2] arrow.t S_2$. We observe that the formula is bult up inductively. If $phi$ is a solution to @eq:traces2, then:
- $phi=U$ a free variable, or
- $phi=diamond_delta phi'$, or
- $phi=eta U. phi'$ where $eta in {mu,nu}$, or
- $phi = phi' arrow.t S_i $, or
- $phi=[phi_1,dots,phi_n]$

We also observe how the semantics of $phi$ are defined. For a valuation $V: Var -> (S -> Sigma^omega)$, the semantics of a formula $||phi||_V: S -> cal(P)(Tree_Sigma)$ are:

- $||U||_V= V(U)$ for $u$ a free variable,
- $||diamond_delta phi||(s)={(sigma,(tau_1,dots,tau_(|sigma|))) | exists (s_1,dots,s_(|sigma|)) in delta(s)(sigma)[ forall i[ tau_i in ||phi'||_(V)(s_i)]] }$,
- $||nu U. phi|| = lfp(lambda u. ||phi||_(V[U |-> u]))$,
- $||mu U. phi|| = text("gfp")(lambda u. ||phi||_(V[U |-> u]))$,
- $||phi arrow.t S_i||_V=||phi||_V arrow.t S_i$ (function restriction),
- $||phi||_(V)(s) = cases(||phi_1||_(V)(s) "if " s in S_1, dots.v, ||phi_n||_(V)(s) "if " s in S_n)$

So we convert the closed formula from the system of equations to a modal mu-calculus formula and prove that the semantics coincide:

#definition[For a closed formula $phi$ solution to @eq:traces2, we define the closed modal mu calculus formula (@def:modal) $overline(phi)$:
  - $phi=u$ a free variable then $overline(phi)=u$ also a free variable
  - $phi=diamond_delta phi'$ then $overline(phi)=diamond overline(phi')$
  - $phi=eta u. phi'$ for $eta in {mu,nu}$ then $overline(phi)=eta u . overline(phi')$
  - $phi = phi' arrow.t S_i $ then $overline(phi)=p_i and overline(phi')$
  - $phi=[phi_1,dots,phi_n]$ then $overline(phi)=(p_1 and overline(phi_1)) or ... or (p_n and overline(phi_n))$
]


#lemma()[
  For a closed formula $phi$ solution to @eq:traces2 and a valuation $V: Var -> (S -> cal(P)(Tree_Sigma))$, $s in S, tau in Tree_Sigma$:

  $
    tau in ||phi||_(V) (s) <=> (s,tau) in ||overline(phi)||^(T_A)_overline(V)
  $

  where $overline(V)(U)={(s,tau)| s in S, tau in V(U)(s)}$
] <lemma:1>

The proof is relatively straightforward by performing induction on the formula $phi$ and can be found in @appendix:lemma:1.

Next, we apply @th:game to obtain a winning strategy for $V$ on $cal(G)(T_A, overline(phi))$, so our final step is relating such a winning strategy with an accepting run on the Büchi automaton:

#lemma()[
  For a closed formula $phi$ solution to @eq:traces2, V has a winning strategy in the game $cal(G)(overline(phi),T_A)$ from $(overline(phi_i),(s,tau))$ iff the Büchi automaton $A$ accepts the tree $tau$ from $s$, i.e. $tau in L(A)(s)$.
] <lemma:3>

The proof follows from a couple of key observations: the observation that the choices $V$ makes when $phi=diamond phi' $ correspond to what state to pick for the run $rho$ of $A$ on $tau$; the transition $R$ can pick when $phi= box phi'$ correspond to checking whether every infinite branch in the run has the maximum occuring priority even; and finally that the even priorities in the game correspond to the accepting states in the automaton. The concrete proof can be found in @appendix:lemma:3. However, as noted before, the proof of this lemma is only for the Büchi case (two parities). The hard step for higher priorities is reasoning about parity of the subformulas of the closed formula from the system of equations because they get big and convoluted quickly. The parity then depends on the alternation depth of these formulas (see @def:paritygame) which is hard for these large and complicated formulas.

The proof of @th (for Büchi automata on trees) now follows from @lemma:0, @lemma:1, @th:game and @lemma:3.

= Conclusion and Future Work <sec:conclusion>
In this report we have shown a coalgebraic representation of Büchi automata, and more generally, parity tree automata. The construction relies upon two key ideas: working in the Kleisli category for the monad $cal(P)$ and deriving separate commuting diagrams for states with different parities and then utilizing fixed point equations for these different mappings for each parity.

We explained the model in the Kleisli category in @sec:nd by showing how to construct a final coalgebra for finite words for a nondeterministic automaton. Subsequently we constructed a weakly final coalgebra to additionally obtain the infinite words within such a system. Building upon these ideas we derived the coalgebraic construction for parity tree automata in @results:buchi, making use of the modal mu-calculus explained in @sec:modal.

In @sec:new we presented our alternate derivation of the coincidence results in @results:buchi. By applying game semantics we were able to give a more comprehensive proof of the results. Additionally, looking at this result through this alternate angle of game semantics can provide new insights.

Seeing if this alternate derivation can shed new light onto the topic, for example connections to coalgebra automata which are based on game theoretic techniques @kupke2008coalgebraic, is one direction of future work that could build upon this report. Secondly, future work could look into proving @lemma:3 for parity automata. As explained in @sec:new, we were unable to prove this lemma for the most general case due to the complicated nature of the system of equations. Bridging this gap would complete the alternate derivation of the coincidence result for all parity tree automata.


#bibliography("refs.bib", style: "association-for-computing-machinery")

#show: appendix

= Proofs <appendix>
== _Proof of @lemma:0 _ <appendix:lemma:0>
First we unfold some definitions:

$(eta_(Tree_Sigma) d)^(-1)= eta_(Tree_Sigma) (d^(-1))$ where $d^(-1)(tau_1,dots,tau_(|sigma|))= (sigma,(tau_1,dots,tau_(|sigma|))) in Tree_Sigma$.

Let us call $u_1+dots+ u_n=beh$ such that $overline(F)[u_1,dots,u_n]=overline(F)(beh)= lambda_(Tree_Sigma) compose (union.sq_(sigma in Sigma) beh^(|sigma|))$ so and see that $union.sq_(sigma in Sigma) beh^(|sigma|): (union.sq_(sigma in Sigma) S^(|sigma|)) -> (union.sq_(sigma in Sigma) (cal(P)(Tree_Sigma))^(|sigma|))$, maps a tuple of states $(s_1,dots,s_(|sigma|))$ to $(beh(s_1),dots,beh(s_(|sigma|)))$, i.e. to the languages accepted by every state $s_i$. Combining with the natural transformation $lambda: (union.sq_(sigma in Sigma) (cal(P)(Tree_Sigma))^(|sigma|))-> cal(P)(union.sq_(sigma in Sigma) Tree_Sigma^(|sigma|))$ defined by $lambda(Tau_1,dots,Tau_(|sigma|))={(tau_1,dots,tau_(|sigma|))| tau_i in Tau_i }$ we get $overline(F)[u_1,dots,u_n](s_1,dots,s_(|sigma|))={(tau_1,dots,tau_(|sigma|)) | tau_i in beh(s_i)}$

$c_i= c compose kappa_i: S_i -> cal(P)(union.sq_(sigma in Sigma) S^(|sigma|))$ in terms of the automaton is defined as $c_(i)(s)={S'| sigma in Sigma, S'=(s_1^',dots,s_(|sigma|)^') in delta(s)(sigma)} in cal(P)(union.sq_(sigma in Sigma) S^(|sigma|)) $ for $s in S_i$, i.e., tuples of succesor states for each $sigma$.

Combining these, and writing out the Kleisli composition in terms of functions in *Sets* we get:

$
  (eta_(Tree_Sigma) d)^(-1) dot.circle overline(F)[u_1,dots,u_n] dot.circle c_i = mu_(Tree_Sigma) compose cal(P)(eta_(Tree_Sigma) compose d^(-1)) compose (mu_(union.sq_(sigma in Sigma) Tree_Sigma^(|sigma|)) compose cal(P)(lambda compose union.sq_(sigma in Sigma) beh^(|sigma|)) compose c_i).
$

Observing that $mu_(Tree_Sigma) compose cal(P)(eta_(Tree_Sigma) compose d^(-1)) = cal(P)(d^(-1)))$, letting $u_1+dots+u_n=beh$ again and combining $cal(P)(lambda compose (union.sq_(sigma in Sigma) beh^(|sigma|)))$ and $c_i$ by using our observations from above we obtain, for an $s in S_i$:

$
  mu_(Tree_Sigma) compose cal(P)(eta_(Tree_Sigma) compose d^(-1)) compose (mu_(union.sq_(sigma in Sigma) Tree_Sigma^(|sigma|)) compose cal(P)(lambda compose union.sq_(sigma in Sigma) beh^(|sigma|)) compose c_i)(s) \
  = cal(P)(d^(-1))({(tau_1,dots,tau_(|sigma|)) | sigma in Sigma, (s^'_1,dots,s^'_(|sigma)) in delta(s)(sigma), tau_i in [beh](s^'_(i)) })\
  = {(sigma,(tau_1,dots,tau_(|sigma|))) | sigma in Sigma, (s^'_1,dots,s^'_(|sigma)) in delta(s)(sigma), tau_i in [beh](s^'_(i)) } = diamond_delta (beh)(s)
$ #h(1fr) $square$

#let ubar = $overline(U)$
#let vbar = $overline(V)$
#let wbar = $overline(W)$
#let ybar = $overline(Y)$
#let dd = $diamond_delta$


== _Proof of @lemma:1 _ <appendix:lemma:1>
We prove this by induction on the formula $phi$. The base case is $phi=U$ a free variable:

$tau in ||U||_(V)(s)=V(U)(s) <-> (s,tau) in overline(V)(U) = ||U||^(T_A)_(overline(V))$

Induction step:

- $phi=mu U. phi'$:

We have to show $tau in ||mu U. phi'||_(V)(s)=lfp(lambda u. ||phi'||_(V[U |-> u])) <=> (s,tau) in ||mu U. overline(phi')||_(overline(V))=lfp (lambda u. ||overline(phi')||_(overline(V)[U |-> u]))$. Let $W= lfp(lambda u. ||phi'||_(V[U |-> u]))$. We define $overline(W)={(s,tau) | s in S, tau in W(s)}$ and show $W= lfp(lambda u. ||phi'||_(V[U |-> u]))<=>overline(W)= lfp(lambda u. ||overline(phi')||_(V[U |-> u]))$. For this we first prove that $W$ is a fixed point iff $overline(W)$ is a fixed point:

Assume $W$ is a fixed point, so $||phi'||_(V[U |-> W]) = W$. We observe that for a valuation $V$ and $V'$ where $V'=V[U|->W]$, we have the converted valuation $overline(V')=overline(V)[U |-> overline(W)]$. We use this to incite the IH to get $w in ||phi'||_(V[U|->W]) <=> (s,tau) in ||overline(phi')||_(overline(V)[U |-> overline(W)])$. Using this we get $(s,tau) in ||overline(phi')||_(overline(V)[U|-> overline(W)]) <=> w in ||phi'||_(V[U |-> W])(s)=W(s) <=> (s,tau) in overline(W)$, so $||overline(phi')||_(overline(V)[U |->overline(W)])= wbar$, so $wbar$ is a fixed point.

Now assume $overline(W)$ is a fixed point, so $||overline(phi')||_(overline(V)[U |-> wbar]) = wbar$. Then, for $s in S$, $W(s)={s | (s,tau) in overline(W)}$. Applying IH like the previous case again we obtain $w in ||phi'||_(V[U |-> W])(s) <=> (tau,s) in ||overline(phi')||_(overline(V)[U |-> overline(W)])= W <=> tau in W(s) $. So $w in ||phi'||_(V[U |-> W])(s) <=> tau in W(s)$ for all $s in S$, so $||phi'||_(V[U |-> W])=W$, so $W$ is a fixed point.

Next, we show that $W$ is the _least_ fixed point iff $overline(W)$ is the _least_ fixed point:

Assume $W$ is a lfp, from above we know that $wbar$ is a fixed point. Take some other fixed point $ybar$, i.e. $||overline(phi')||_(overline(V)[U|->ybar])=ybar$. Now, again inciting what we showed above, we know $Y$ is a fixed point, so $||phi'||_(V[U|->ybar])=ybar$. So because $W$ is the lfp, for all $s$, $W(s)subset.eq Y(s)$. From this it follows that $(s,tau) in wbar -> tau in W(s) -> tau in Y(s) -> (s,tau) in ybar$, so $wbar subset.eq ybar$. So $wbar$ is the least fixed point.

For the other direction, assume $overline(W)$ is a least fixed point. Then $W$ is a fixed point. Take some other fixed point $Y$, i.e. $||phi'||_(V[U|->Y])=Y$, then $ybar$ is a fixed point. So because $wbar$ is the lfp, we have $wbar subset.eq ybar$. Now for any $tau,s$ we have $tau in W(s) -> (s,tau) in wbar -> (s,tau) in ybar -> tau in Y(s)$. So $W subset.eq Y$.

- $phi=nu U. phi'$:

This case is a analagous to the $mu$ case. The first part proving $W$ is a fixed point iff $wbar$ is a fixed point, and for proving $W$ is a _greatest_ fixed point iff $wbar$ is too you reason in the opposite direction as for $mu$.

- $phi=diamond_delta phi'$: \
$
  tau &in ||diamond_delta phi'||_(V)(s)\
  &= {(sigma,(tau_1,dots,tau_(|sigma|))) | exists (s_1,dots,s_(|sigma|)) in delta(s)(sigma)[ forall i[ tau_i in ||phi'||_(V)(s_i)]] }\
  &=^(I H) {(sigma,(tau_1,dots,tau_(|sigma|))) | exists (s_1,dots,s_(|sigma|)) in delta(s)(sigma)[ forall i[ (s_i,tau_i) in ||overline(phi')||_(overline(V))]] }\
  &=^* {(sigma,(tau_1,dots,tau_(|sigma|))) | exists (s_1,dots,s_(|sigma|)) in delta(s)(sigma)[ ((s_1,dots,s_(|sigma|)), (sigma,(tau_1,dots,tau_(|sigma|)))) in ||square overline(phi')||_(overline(V))] }\
  &<-> (s,tau) in {(s,(sigma,(tau_1,dots,tau_(|sigma|)))) | exists (s_1,dots,s_(|sigma|)) in delta(s)(sigma)[ ((s_1,dots,s_(|sigma|)), (sigma,(tau_1,dots,tau_(|sigma|)))) in ||square overline(phi')||_(overline(V))] }\
  &=^(**) ||diamond square overline(phi')||^(T_A)_(overline(V))
$
- $phi = phi' harpoon.tr S_i$: \
$tau in ||phi' harpoon.tr S_i||_(V)(s) <-> s in S_i and tau in ||phi'||_(V)(s) <->^(I H)s in S_i and (s,tau) in ||overline(phi')||_(overline(V)) <-> (s,tau) in ||p_i and overline(phi')||_(overline(V))$
- $phi= [phi_1,dots,phi_n]$:
$||phi||_(V)(s) = cases(||phi_1||_(V)(s) "if " s in S_1, dots.v, ||phi_n||_(V)(s) "if " s in S_n)$, so let $tau in ||phi||_(V)(s)$ for $s in S_i$, then $tau in ||phi_i||_(V)(s)$ so by IH $(s,tau) in ||overline(phi_i)||_(overline(V))(s)$, and because $s in S_i$, $(s,tau) in S_i$, $(s,tau) in ||p_i and overline(phi_i)||_(overline(V))(s)$ and thus $(s,tau) in ||(p_1 and phi_1) or ... or (p_n and phi_n)||_overline(V)=||overline(phi)||_overline(V)$.

Now $(s,tau) in ||overline(phi)||_overline(V) = ||(p_1 and overline(phi_1)) or ... or (p_n and overline(phi_n))||_overline(V)$. Take $i$ such that $(s,tau) in ||p_i and overline(phi_i)||_overline(V)$ then we have $s in S_i$ and (by IH) $w in ||phi_i||_(V)(s)$, and by definition of $||[phi_1,...,phi_n]||$ then $tau in ||phi||_(V)(s)$.


== _Proof of @lemma:3 _ <appendix:lemma:3>
// First show (observe) that the transitions in the game for $diamond$ correspond exactly to those in the automaton ($<->$).

Observe the closed formulas for @eq:traces2 $l_sol^1$ and $l_sol^2$:
- #[$l_sol^1 =  mu u_1.diamond^1_delta [u_1, nu u_2. diamond^2_delta [(mu u_1^'. diamond^1_delta [u_1^', u_2]), u_2]
  )$,

    so $overline(phi_1)=mu u_1. p_1 and diamond ((p_1 and u_1) or (p_2 and nu u_2. (p_2 and diamond((mu u_1^'.p_1 and diamond((p_1 and u_1^') or (p_2 and u_2))) or (p_2 and u_2)))))$. We observe that $Omega(mu u_1. ...)=1$, $Omega(nu u_2. ...)=2$ and $Omega(mu u_1^'. ...)=1$.]
- #[$l_sol^2 = nu u_2. diamond^2_delta [(mu u_1^'. diamond^1_delta [u_1^', u_2]), u_2]$

    so $overline(phi_2)=nu u_2. (p_2 and diamond((mu u_1^'.p_1 and diamond((p_1 and u_1^') or (p_2 and u_2))) or (p_2 and u_2))))$. We observe that $Omega(mu u_2. ...)=2$, $Omega(nu u_1. ...)=1$.
  ]

Assume player $V$ has a winning strategy for $cal(G)(overline(phi_i),T_A)$ from $(overline(phi_i),(s,tau))$. Observe that through V's choices when $phi=diamond phi'$, $(diamond phi', (s,(sigma,(tau_1,dots,tau_(|sigma|)))) -> (phi', ((s_1^',dots, s_n^'), (tau_1,dots,tau_(|sigma|))))$ tell how to construct the run $rho$ on $A$. Because $V$ has a winning strategy, R can pick whatever transition it wants when $phi=box phi'$ and the play will be won by $V$, which means the maximal priority of the states in $cal(G)(overline(phi_i), T_A)$ is even. This corresponds to checking an infinite branch of the run $rho$ of $A$ on $tau$ and because the even parity in the game corresponds to $S_2$ in the automaton, the maximum priority of the states in $A$ occuring infinitely often in every infinite branch of the run $rho$ of $A$ on $tau$ is even, which means $tau$ is accepted by $T$ from state $s$.

The other way is similar. We again osbserve that the choice $V$ has to make when $phi=diamond phi'$ is decided by the run of $A$ on $tau$, and the fact that regardless of the transitions $R$ picks when $phi = box phi'$ the play is winning by $V$ follows from the fact that for every infinite branch of the run the maximum priority of the states occuring infinitely often is even, which corresponds to the even parities in the game, and thus the play in the game is winning by $V$. Furthermore, note that the choice to pick at $(((p_1 and overline(phi_1)) or ... or (p_n and overline(phi_n))), (s, tau))$ simply depends on $i$ such that $s in S_i$, and that also makes sure that $R$ cannot pick the left formula in the formula $p_i and overline(phi_i)$ to win that way becasue $s in S_i$.
