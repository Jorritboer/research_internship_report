#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge
#import "@preview/ctheorems:1.1.3": *

#show: thmrules.with(qed-symbol: $square$)

#let mythmbox(..args) = thmbox(..args, inset: (x: 1em))
#let mythmproof(..args) = thmproof(..args, inset: 0em)

#let theorem = mythmbox("theorem", "Theorem", base: "heading", base_level: 1)
#let lemma = mythmbox("theorem", "Lemma", base: "heading", base_level: 1)
#let definition = mythmbox("theorem", "Definition", base: "heading", base_level: 1, inset: 0em)
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
#let DelSt = text("DelSt")
#let beh = math.sans("beh")
#let Klp = $cal("Kl")(cal(P))$
#let tr = beh
#let lfp = text("lfp")
#let Var = math.italic("Var")
#let cons = math.sans("cons")


// Title row.
#align(center)[
  #text(20pt, weight: 700, "Coalgebraic Representation of Nondeterministic Systems and Büchi Automata")

  #text(14pt, weight: 600, "Midterm Report Research Internship")

  Jorrit de Boer
]

#set heading(numbering: "1.1")
#set par(justify: true)


#align(center)[
  #set par(justify: false)
  // #set text(style: "italic")
  *Abstract.*
  _We provide an explanation of existing literature for describing Büchi automata coalgebraically. To do this we also explain modal mu-calculus and a coalgebraic model of nondeterministic systems. Finally, we outline our plans for the rest of the research internship. _
]

= Introduction

_Büchi automata_ and _nondeterministic systems_ are crucial in theoretical computer science for modeling and verifying systems with infinite behaviors @gradel2003automata@Vardi1996. Nondeterministic systems capture uncertainty and multiple outcomes, and are used in models like concurrent processes and nondeterministic Turing machines. Büchi automata, which are often also nondeterministic, handle infinite sequences of events, crucial for verifying systems that run indefinitely, such as operating systems or network protocols.

_Coalgebra_ provides an effective framework for modeling state-based, dynamic systems. Techniques such as _coinduction_ allow for reasoning about infinite structures, while _bisimulation_ offers a formal way to establish behavioral equivalence between systems @rutten2000universal. By modeling Büchi automata coalgebraically, we unify these powerful tools for reasoning about infinite behaviors and nondeterminism.

The main goal of this report is to provide an understanding of the coalgebraic construction of Büchi automata described in @urabe2016coalgebraic. To do so we also explain _modal mu-calculus_, a system to verify properties of transition systems, and provide a coalgebraic model of nondeterministic systems, upon which the construction for the Büchi automata builds. By outlining these concepts we advance our first goal of the research internship, which is to gain an understanding of the current research into this topic.

Next to providing an overview of the available literature, we outline our plan for the rest of the internship. Our goal is to use _game semantics_ as an alternative framework to derive the coalgebraic representation of Büchi automata. Game semantics is a framework of describing a system in terms of a two-player game between a _verifier_ and a _refuter_ who want to verify, respectively refute, a statement @gradel2003automata. By utilizing game semantics we hope to provide a more intuitive proof of the existing results.

The document is outlined as follows. In @sec:background we provide some background and relevant definitions for the rest of the report. In @chap:results we give the main results from the studied literature, which is divided into: modal mu-calculus in @sec:modal, coalgebraic model of nondeterministic systems in @sec:nd, and the coalgebraic model of Büchi automata in @results:buchi. Finally, in @sec:conclusion we summarize the results and give our plans for the rest of the internship.

// #outline(depth: 2)

// #show heading.where(depth: 1): body => {
//   pagebreak(weak: true)
//   body
// }

= Background <sec:background>
// In this section we present the relevant background and definitions required for the rest of the report.

== Büchi Automata <sec:buchi>

Let us consider a very simple motivating example for a Büchi automaton, shown in @img:buchi.

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

This behavior can be modeled using a Büchi automaton. A Büchi automaton, namely, is an automaton which models infinite behavior, and accepts those words for which there is path through the automaton where the transitions are labeled by the letters of the words, an there is an accepting state that the path moves through infinitely many times. In this example, we make the `idle` state accepting, so the automaton accepts those words that always take the `return` transition again, and thus do not process indefinitely.

We can now give a formal definition of a Büchi automaton, and its _accepted language_:

#definition[
  A (nondeterministic) Büchi Automaton @gradel2003automata is a tuple $chi=angle.l X, Sigma, delta, s, F angle.r$, with $X$ a set of states, $Sigma$ the alphabet, $s subset.eq X$ the set of initial states, $delta : X times Sigma -> cal(P)(X)$ the transition function, $F subset.eq X$ the set of _final_ (or _accepting_) states.
]

A run of a Büchi Automaton $chi$ is $(x_0,sigma_0)(x_1,sigma_1)... in (X times Sigma)^omega$, such that for every $n in omega$, $x_(n+1) in delta(x_n,sigma_n)$. We denote the set of runs of the Büchi Automaton $chi$ as $Run_chi$.

A run is accepted if it passes through an accepting state infinitely many times. I.e. a run $rho=(x_0,sigma_0)(x_1,sigma_1)...$ is accepted if ${x_i | x_i in F}$ is an infinite set. $AccRun_chi$ is the set of accepted runs of $chi$. $Run_(chi,X')$ is the set of runs starting in $X'$, i.e. $(x_0,sigma_0)(x_1,sigma_1)... in Run_(chi,X)$ if $x_0 in X'$. The set $AccRun_(chi,X')$ is defined the same way. The map $DelSt: Run_chi -> Sigma^omega$ 'deletes' the states from a run and returns an $omega$-word. So $DelSt((x_0,sigma_0)(x_1,sigma_1)...)=sigma_0 sigma_1...$. Naturally, the set of accepted language of a Büchi Automaton can then be defined as $text("Lang")(chi)=DelSt(AccRun_(chi,s))$.


Indeed we now see that the accepted language for the example automaton is $(mono("request") dot mono("process")^*dot mono("return"))^omega$. I.e. the machine gets a request, processes for at most some _finite_ number of transitions and then returns some result. It does not get stuck processing indefinitely.

== Fixed Points
// maybe iets over dat we niet in heel veel detail gaan?
Crucial for the next section, @sec:modal about modal mu-calculus, is reasoning about _fixed points_ of _monotone_ functions. We briefly recall the important definitions and theorems.

#definition[
  A _complete lattice_ is a partially ordered set $angle.l L, <= angle.r$ such that every subset $M subset.eq L$ has a least upper bound $or.big M$ and greatest lower bound $and.big M$. Specifically, the whole set $L$ has a least and greatest element, which we denote $and.big L = bot$ and $or.big L = top$, respectively.
]

In this report we usually deal with the partially ordered set of the powerset of some set and ordering given by inclusion. Indeed, for a set $S$, $angle.l cal(P)(S), subset.eq angle.r$ is a complete lattice. For $U subset.eq cal(P)(S)$, $or.big U = union.big U$, and $and.big U = sect.big U$. The least and greatest elements are $emptyset$ and $S$, respectively.

#theorem([Knaster-Tarski Fixed Point Theorem #cite(<arnold2001rudiments>, supplement: "Theorem 1.2.8")])[
  Let $angle.l L, <= angle.r $ a complete lattice and $f:L->L$ monotone ($f(x) <= f(y)$ when $x<=y$). Then, the set of fixed points ${x in L|f(x)=x}$, is a complete lattice. Particularly, the function has a _least fixed point_ (lfp) and a _greatest fixed point_ (gfp).
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

#theorem([#cite(<arnold2001rudiments>, supplement: "Theorem 1.2.11")])[
  There exists an ordinal $kappa$, such that $f^kappa=f^(kappa+1)$, which implies that $f^kappa$ is a fixed point of $f$. Furthermore, $f^kappa$ is the least fixed point of $f$.
  The dual process, beginning from $top$ and moving downward, constructs the greatest fixed point of $f$.
] <th:knaster-tarski2>

== Modal Mu-Calculus <sec:modal>
Modal mu-calculus is a powerful framework, used to verify properties of transition systems @gradel2003automata@arnold2001rudiments. We use it in @results:buchi to select the right accepting words for our coalgebraic system. In this section we give a concrete definition of modal mu-calculus formulas and provide intuition on how to use it to verify certain properties.

In this section we will consider _labeled transition systems_ (LTS) for which we will verify some properties. These systems are a little bit different than those we consider in the rest of the report, but they are useful for explaining modal mu-calculus. Concretely, an LTS is a tuple $angle.l X,Sigma,delta, italic("Prop"), rho angle.r $. Here $X$ is the set of states, $Sigma$ the set of labels, $delta : X times Sigma -> cal(P)(X)$ the transition function (we write $x ->^a y$ for $y in delta(x)(a)$), _Prop_ the set of atomic propositions, and $rho:italic("Prop")->cal(P)(X)$ which interprets the atomic propositions. Note that you can see an LTS as a nondeterministic finite automaton without accepting states where the states are labeled by atomic propositions $cal(P)(italic("Prop"))$.


#definition[
  A modal mu-calculus formula is defined by the grammar:
  $
    phi := P | Z | phi_1 and phi_2 | phi_1 or phi_2 | [a] phi | angle.l a angle.r phi | not phi | mu Z. phi | nu Z.phi
  $
  where $P in italic("Prop")$ is an atomic proposition, $a in Sigma$ a label, and $Z in italic("Var")$ which is a set of second order variables. We require that in $nu Z.phi$ and $mu Z.phi$, every occurance of $Z$ in $phi$ is in the scope of an even number of negations, such that that $phi$ is a monotone function.
]

Note that you could define the modal mu-calculus without the $or$, $angle.l a angle.r$, and $nu$ operators, and define these instead in terms of the other operators, but we include them in the definition for legibility. _this time whole semantics?_

#definition[We define the semantics of a modal mu-calculus formula for an LTS T, and an assignment $V: italic("Var")->cal(P)(X)$:
  $
    ||P||^T_V & := rho(P)\
    ||Z||^T_V & := V(Z) \
    ||not phi||^T_V & := S \\ ||phi||^T_V\
    || phi_1 and phi_2 ||^T_V & := ||phi_1||^T_V sect ||phi_2||^T_V \
    || phi_1 or phi_2 ||^T_V & := ||phi_1||^T_V union ||phi_2||^T_V \
    || [a] phi ||^T_V &:= {x | forall y in X. x->^a y => y in ||phi||^T_V} \
    || angle.l a angle.r phi ||^T_V &:= {x | exists y in X. x->^a y => y in ||phi||^T_V} \
    || mu Z.phi ||^T_V &:= italic("lfp")(lambda U. ||phi||^T_(V[Z |-> U])) = sect.big { U subset.eq X | U subset.eq ||phi||^T_(V[Z |-> U]) }\
    || nu Z.phi ||^T_V &:= italic("gfp")(lambda U. ||phi||^T_(V[Z |-> U])) = union.big { U subset.eq X | ||phi||^T_(V[Z |-> U])subset.eq U }
  $
  where $V[Z|->U]$ is the valuation $V$ except that $Z$ maps to $U$.
]

We do not give a formal definition of the semantics of the formulas for an LTS, but rather give an informal and intuitive explanation, see @arnold2001rudiments@gradel2003automata for the formal definition. We want to say whether in an LTS $T$ a formula $phi$ holds in a state $x$, which we denote $x tack.r.double phi$. The semantics are then roughly as follows:
- $x tack.r.double P$, if the atomic proposition $P$ holds in $x$;

- $x tack.r.double phi_1 and phi_2$, $x tack.r.double phi_1 or phi_2$, if in state $x$ both or either, respectively, formulas $phi_1$ and $phi_2$ hold;
- $x tack.r.double [a]phi$ if for all $a$ transitions taken from $x$, $phi$ holds in the next state;
- $x tack.r.double angle.l a angle.r phi$ if there is some $a$ transition from $x$ where $phi$ holds after the transition;
- $x tack.r.double mu Z. phi$, if $x in italic("lfp")(lambda U. ||phi||[Z |->U])$, i.e. $x$ is in the least fixed point of the monotone function that takes $U$ and replaces very occurance of $Z$ in $phi$ with $U$. Again, this is not a formal definition. The $nu$ operator is defined analogously for the greatest fixed point. We will see that, intuitively, the $mu$ operator is for finite looping and $nu$ is for infinite looping. To make this clear, let us look at the LTS given in @img:lts, and consider some examples of modal mu-calculus formulas.

#figure(
  diagram({
    node((-0.5, 0), $emptyset$)
    node((0, 0), [$x_0$], name: <x0>, shape: circle, stroke: .5pt)
    node((1, -.5), [$x_1$], name: <x1>, shape: circle, stroke: .5pt)
    node((1.5, -.5), ${p}$)
    node((1, .5), $x_2$, name: <x2>, shape: circle, stroke: .5pt)
    node((1.5, .5), ${q}$)

    edge(<x0>, <x1>, $a$, "->")
    edge(<x1>, <x2>, $a$, "->")
    edge(<x0>, <x2>, $a$, "->", bend: +15deg)
    edge(<x2>, <x0>, $a$, "->", bend: +15deg)
  }),
  caption: [Example of an LTS. The sets next to the states denote the atomic propositions that hold in that state.],
) <img:lts>

#let holds = $tack.r.double$

We have $x_0 tack.r.double angle.l a angle.r p$, because there is an $a$ transition that takes us to a state where $p$ holds, namely $x_0 ->^a x_1$, because $x_1 tack.r.double p$. We, however, do not have $x_0 holds [a]p$, because $x_0 ->^a x_2$ and $x_2 tack.r.double.not p$.

To observe that $mu$ incites finite looping, we look at the fact that $x_0 holds mu Z.q or [a]Z$. This roughly means that all $a$ paths have $q$ eventually, which we can see holds in @img:lts. To more formally show that this holds, we make use of the method of constructing least and greatest fixed points in @th:knaster-tarski2. The function we are calculating the lfp for is $f:= lambda U. ||q|| union ||[a]U||$. The first iteration yields $f^1=f(emptyset)={x_2}$, because $x_2 holds q$. Continuing, $f^2={x_1,x_2}$ and $f^3={x_0,x_1,x_2}=f^4$. So the lfp is the entire set of states $X$, and thus $x_0 holds mu Z. q or [a]Z$.

Next we look at $nu$, which can be used for infinite looping. We show that $x_0 holds nu Z. angle.l a angle.r Z$. This intuitively means that there exists an infinite path of $a$s. Indeed, we observe there are multiple such paths, also starting at $x_0$. We confirm by computing the gfp: $f^1=f(X)=angle.l a angle.r X=X$. Dually, observe that the lfp of this formula is $f^1(emptyset)=emptyset$. So we do not have $x_0 holds mu Z. angle.l a angle.r Z$. This confirms the intuition given above that $mu$ is for finite looping: there has to be some end point of the loop.

We briefly discuss here the game semantics view of deciding whether $x holds phi$. We do not go into much detail, but this is to introduce the topic and show what we want to look into applying for the coalgebraic representation of the Büchi automaton as we describe in @sec:conclusion. We can construct a two player game between a verifier and a refuter, who want to verify, respectively, refute $x holds phi$. For example, if $phi=phi_1 or phi_2$, only one of the two options has to hold, so the verifier can choose which one they will verify. If $phi=phi_1 and phi_2$, only one of the two has to _not_ hold in order to refute $x holds phi$, so the refuter can pick which one the verifier has to verify holds, which the refuter thinks they cannot. Analogously for $angle.l sigma angle.r phi$ and $[a] phi$ where the verifier can pick a $sigma$ transition to verify for $angle.l sigma angle.r phi$, and the refuter can pick a transition to refute for $[sigma]phi$. If we work this out more, we can prove that $x holds phi$ iff there is a winning strategy for the verifier, and $x tack.r.double.not phi$ iff the refuter has a winning strategy, see @gradel2003automata for more details.

=== System of Equations

Next we introduce a system of equations for alternating fixed points. We only show how such a system works for two equations to save space and because that is all we use in the rest of the report. For more detail into this specific topic see @arnold2001rudiments@urabe2016coalgebraic.

#definition[
  Let $L_1,L_2$ be partially ordered sets. An _equational system_ is a system of two equations

  $
    u_1 =_eta_1 f_1(u_1,u_2) #h(3em) u_2 =_eta_2 f_2(u_1,u_2)
  $
  where $u_1,u_2$ are variables, $eta_1,eta_2 in {mu,nu}$, and $f_i: L_1 times L_2 -> L_i$ are monotone functions. The solution to the system is defined by the following set of steps:

  The intermediate solution $l^((1))_1 := eta_1 u_1. f_1(u_1,u_2)$, where we take the lfp if $eta_1=mu$ and gfp if $eta_1=nu$. Note that $l^((1))_1:L_2 -> L_1$.

  The solution to the second equation is then given by $l^(sol):= eta_2 u_2. f_2(l^((1))_1(u_2), u_2)$, where again we take the lfp if $eta_2=mu$, and gfp if $eta_2=nu$. The solution to the first equation is then $l^sol_1 = l^((1))_1(l^sol_2)$.
] <def:eq>

== Parity Games
#definition("Parity Game")[
  A parity game is a tuple $((V_1,V_2),E,Omega)$, where $V=V_1 union.sq V_2$ is the set of states, where $V_1$ are the states where player 1 can pick the next transition, and $V_2$ player 2. $E subset.eq V times V$ are transitions between the states. $Omega:V->bb(N)$ is the parity function, which determines the winner for infinite games.

  A play of the game is a sequence of states $v_1,v_2,dots in V^infinity$ which conform to the transitions. A finite play is won by a player if the other player gets stuck, i.e. has no moves from a position. An infinite play $pi=v_1,v_2,dots$ is won by player 1 if $max{Omega(v) | v "occurs infinitely often in" pi}$ is even, else player 2 wins.
]

#definition([Parity Game for Modal $mu$-Calculus on Transition System. Definition 10.14, Remark 10.15 @gradel2003automata])[
  For a transition system $T=(S,->,lambda)$ and a modal $mu$-calculus formula $phi$, we define the game $cal(G)(phi,T)=((V_1,V_2),E,Omega)$ where:
  - #[$V=V_1 union.sq V_2= {phi' | phi' " is a subformula of " phi} times S$ where the formula determines whether player 1 or 2 can move. For a vertex $(psi,s) in V$:
      - #[$(psi,s) in V_1$, i.e. player 1 can move if
          - $psi= psi_1 or psi_2$
          - $psi= diamond psi'$
          - $psi= eta Z. psi'$ for $eta in {mu,nu}$
          - $psi=Z$ for $Z subset.eq cal(P)(S)$ a fixed point variable
          - $psi = p$ for $p$ a propositional variable with $p in lambda(s)$.
        ]
      - #[$(psi,s) in V_2$, i.e. player 2 can move if
          - $psi=psi_1 and psi_2$
          - $psi = p$ for $p$ a propositional variable with $p in.not lambda(s)$.
        ]
    ]
  - Edges:
    - $(psi_1 or psi_2,s)->(psi_1,s)$ and $(psi_1 or psi_2,s)->(psi_2,s)$
    - $(psi_1 and psi_2,s)->(psi_1,s)$ and $(psi_1 and psi_2,s)->(psi_2,s)$
    - $(diamond psi, s)->(psi,s')$ for any $s'$ such that $s -> s'$ in $T$.
    - $(eta Z. psi, s)-> (psi, s)$ and $(Z,s)->(psi,s)$ for $eta in {mu,nu}$
  - $Omega$: (more precise definition needed)
    - $Omega((mu Z.psi,s))= $ the smallest odd number greater or equal than the (proper) alternated $mu slash nu$ operators in $psi$.
    - $Omega((mu Z.psi,s))= $ the smallest even number greater or equal than the (proper) alternated $mu slash nu$ operators in $psi$.
    - $Omega((psi,s))=0$ iff $psi$ is not a $mu$ or $nu$ formula.
]


= Coalgebraic Representation of Büchi Automata <chap:results>
== Finite Behavior Nondeterministic Systems <sec:nd>
In this section we present a coalgebraic representation of nondeterministic systems. The next section for Büchi automata builds upon this construction.

=== Deterministic Automata <sec:d>

First we consider a deterministic finite automaton, $angle.l X, Sigma, delta, o angle.r $ with $X$ the states, $Sigma$ the alphabet, $delta: X times Sigma -> X$ the transition function, and $o: X -> 2$ with $2={0,1}$, the output function determining if a state is final. Such an automaton can be represented by a coalgebra $c: X -> 2 times X^Sigma$ for the functor $F(X)=2 times X^Sigma$. This a very useful construction because a final coalgebra for this functor is carried by $2^Sigma^*$, and the unique coalgebra homomorphism to this final coalgebra captures exactly the language accepted by a state @rutten2000universal. This is shown in the commuting diagram:

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

Working out the paths through the diagram we obtain that
- $beh(x)(epsilon)=o(x)$, and
- $beh(x)(sigma w)=beh(delta(x)(sigma))(w)$,

for $x in X$, $sigma in Sigma$, $w in Sigma^*$. So $beh(x)$ accepts the empty word if $x$ is a final state, and accepts $sigma w$ if $delta(x)(sigma)$ accepts $w$. Which is precisely the language accepted by state $x$ in the deterministic finite automaton!

=== Finite Behavior Nondeterministic Systems <sec:finite>

We would like to do the same thing for nondeterministic systems, but we run into a problem, which is highlighted by the following example, shown in @img:nd.

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
// ]

The system is an LTS without atomic propositions but with termination, denoted by the transition to $checkmark$. It is a nondeterministic system because in $x_0$ there are two transitions for $a$, and in $x_1$ and $x_2$ the system can transition back to itself or to $checkmark$. Intuitively, the finite words accepted by the system from state $x_0$ should be
$ tr(x_0) = {a, a b, a b b, ...} union {a, a c, a c c, ...}. $

This transitions system might be modeled by a coalgebra $c: X -> cal(P)(1 + Sigma times X)$, i.e. for every state some subset of a terminating transition or reading a letter and transitioning to another state. The problem is that this functor $F X = cal(P)(1 + Sigma times X)$ does not have a final coalgebra. Because, by Lambek's lemma, such a final coalgebra $z: Z -> cal(P)(1+ Sigma times Z)$ for some carrying object $Z$, would have to be an isomorphism @awodey2010category. But an isomorphism $Z tilde.equiv cal(P)(1 + Sigma times Z)$ would imply a bijection between $Z$ and $cal(P)(Z)$, which cannot exist.

The solution, as given by Hasuo et al. @hasuo2007generic, is to work in the Kleisli category for the monad $cal(P)$. For this to work we have to define some details regarding construction of the coalgebra in the Kleisli Category. We give the resulting commuting diagram to show what we are working towards:

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

Here $c:X -> overline(F)X= cal(P)(1 + Sigma times X)$ will be the coalgebra our nondeterministic system, and $tr_c : X -> A$ in $cal("Kl")(cal(P))$ is the unique map from $X$ to $A$, which contains the finite accepting words in the nondeterministic system. Key here is that because we are working in the Kleisli category the map $tr_c$ is actually a map $tr_c: X -> cal(P)(A)$ in the category *Sets*, which captures exactly the desired finite words, thus solving the problem when trying to obtain the final coalgebra in the category *Sets* directly.

So we need to define the Kleisli Category, and define the right functor in $Klp$ to give us the desired words.

The powerset monad $cal(P)$ is defined by the unit $eta_X : X -> cal(P)(X)$ which sends an element of $X$ to the singleton set, $eta_X (x)={x}$ for $x in X$, and the multiplication $mu_X: cal(P)(cal(P)(X)) -> cal(P)(X)$ which takes the union of the sets, i.e. $mu_X (A) = union.big_(a in A) a$. For a function $f: X -> Y$ we get $cal(P)(f): cal(P)(X) -> cal(P)(Y)$ by $cal(P)(f)(A)= {f(a) | a in A}$. The Kleisli category for this monad is defined as follows:
- *objects*: the same as for *Sets*, sets
- *morphisms*: a morphism $f$ from $X$ to $Y$ in $Klp$ is a maps $f:X-> cal(P)(Y)$ in *Sets*. For morphisms $f: X -> Y$ and $g: Y -> Z$ in $Klp$ (so $f: X-> cal(P)(Y)$ and $g: Y -> cal(Z)$ in *Sets*) we define $(g compose f)$ in $Klp$ as $(mu_Z compose cal(P)(g) compose f)$ in *Sets*. Indeed $(mu_Z compose cal(P)(g) compose f): X -> cal(P)(Z)$, so $(g compose f): X -> Z$ in $Klp$.

Next, we construct our functor in $Klp$, which we call the lifting of $F$ in $Klp$, and denote $overline(F)$. The key here is that because we are working in the Kleisli category, if we use the functor $F X = 1 + Sigma times X$, the coalgebra map $c: X -> F X$, will be a map $c: X -> cal(P)(1 + Sigma times X)=overline(F)X$ in $Klp$, which is what we needed to model a nondeterministic transition.

This works easily on objects, $overline(F)X=F X$, because in the Kleisli category, the objects are the same. But for morphisms we have to do a little bit more work. Observe that because a map $f:X-> Y$ in $Klp$ is a map $f: X->cal(P)(X)$ in *Sets*, applying the functor on the map itself would yield $F f: F X -> F cal(P) (X)$. So what we need is a natural transformation $lambda: F cal(P) => cal(P) F$, such that $1+Sigma times (cal(P)(X)) ->^lambda cal(P)(1+Sigma times X)$. We define this as $* arrow.r.bar {*}$ (note that we use $1={*}$), and $(sigma,S)={(sigma,x)|x in S}$ for $sigma in Sigma$ and $S subset.eq X$. This follows intuitively if you observe that if from state $s$ taking transition $sigma$ takes you to ${x,y,z}$ ($(sigma,{x,y,z}) in c(s)$, or ${x,y,z} in delta(s)(sigma)$), you can also see this as transitions ${(sigma,x),(sigma,y),(sigma,z)}$.

Finally, the main theorem from @hasuo2007generic (Theorem 3.3), and the last ingredient to make the construction work is that the initial algebra for the functor $F$ in sets, gives us the final coalgebra for the lifted functor $overline(F)$ in $Klp$. Specifically, for this functor $F X= 1 + Sigma times X$ and its lifting as described above, the initial $F$-algebra $alpha: F A -> A$ in *Sets* yields a final $overline(F)$-coalgebra in $cal("Kl")(cal(P))$ by:

$ (J alpha)^(-1) = J (alpha^(-1)) = eta_(F A) alpha^(-1) : A -> overline(F)A italic("in") cal("Kl")(cal(P)) $

where $J=eta_(F A)$ is the canonical adjunction associated with the Kleisli category @hasuo2007generic@awodey2010category. This result holds more generally: for the lifting monad $cal(L)$, the subdistribution monad $cal(D)$, and any shapely functor $F$, see @hasuo2007generic for more details.

Let us go back to our concrete example and instantiate the commuting diagram from before. The initial $F$-algebra for our functor $F X = 1 + Sigma times X$ in *Sets* is $[sans("nil"),sans("cons")]: 1 + Sigma times Sigma^* -> Sigma^*$. So we get the commuting diagram

$
  #diagram(
    spacing: 3.5em,
    {
      node((0, 1), $X$, name: <X>)
      node((0, 0), $1 + Sigma times X$, name: <FX>)
      node((1, 1), $Sigma^*$, name: <A>)
      node((1, 0), $1 + Sigma times Sigma^*$, name: <FA>)
      edge(<X>, <FX>, $c$, "->", label-side: left)
      edge(<A>, <FA>, $tilde.equiv$, "-", label-side: left, stroke: 0pt)
      edge(<A>, <FA>, $J [sans("nil"),sans("cons")]^(-1)$, "->", label-side: right)
      edge(<X>, <A>, $text(tr)_c$, "-->", label-side: right)
      edge(<FX>, <FA>, $1 + Sigma times tr_c$, "-->")
      node((2, .5), $italic("in") cal("Kl")(cal(P)).$)
    },
  )
$

Following the paths within the diagram we obtain that

$
  epsilon in tr_c (x) <==> x -> checkmark \
  sigma w in tr_c (x) <==> exists y. (x ->^sigma y and w in tr_c (y)).
$ <eq:finite>

Explained in words, a state accepts the empty word if it can transition to $checkmark$, and it accepts $sigma w$ for $sigma in Sigma$ and $w in Sigma^*$ if it can transition with $sigma$ to a state which accepts $w$. Which is exactly the desired words!

// _should be explained more_

// #definition("LTL")[
// 	A (nondeterministic) Labeled Transition System (LTL) is a tuple $angle.l X,Sigma,delta angle.r$, consisting of a set of states $X$, an alphabet $Sigma$, a transition system $delta: X times Sigma -> cal(P)(X) union {checkmark}$. Where checkmark is explicit termination.
// ]

=== Possibly Infinite Behavior <sec:infinite>
As a step towards infinite words in Büchi automata let us consider infinite words in @img:nd. We can slightly alter our previous construction to additionally obtain infinite words through this system. Concretely, the infinite words for the system in @img:nd for $x_0$ are $a b^omega$ and $a c^omega$.

The intuition for this new construction is as follows. In the previous section we constructed the final coalgebra for the lifted functor $overline(F)$ using the initial $F$-algebra in *Sets*. In the example of the LTS with termination the initial algebra was carried by $Sigma^*$. The final coalgebra in *Sets* for $F$ is carried by $Sigma^infinity=Sigma^* union Sigma^omega$, the set of finite and infinite words. So if we use this final coalgebra instead of the initial algebra, do we obtain both the finite and infinite words?

Consider again the monad $cal(P)$, our functor $F$ (this too holds more general, see @hasuo2007generic@jacobs2004trace), and its lifting in the Kleisli category $overline(F)$. For a final coalgebra $xi: Z-> F Z$, the coalgebra

$ J xi : Z -> overline(F) Z italic("in") Klp $

is _weakly final_. That means, for any coalgebra $c: X -> overline(F)X$, there is a morphism $tr:X -> Z$ in $Klp$ such that the following diagram commutes

$
  #diagram(
    // spacing: 2cm,
    {
      node((0, 1), $X$, name: <X>)
      node((0, 0), $overline(F) X$, name: <FX>)
      node((1, 1), $Z$, name: <Z>)
      node((1, 0), $overline(F) Z$, name: <FZ>)
      edge(<X>, <FX>, $c$, "->", label-side: left)
      edge(<Z>, <FZ>, $tilde.equiv$, "-", label-side: left, stroke: 0pt)
      edge(<Z>, <FZ>, $J xi$, "->", label-side: right)
      edge(<X>, <Z>, $text(tr)_c$, "~>", label-side: right)
      edge(<FX>, <FZ>, $overline(F)(text(tr)_c)$, "~>")
      node((2, .5), $italic("in") cal("Kl")(cal(P)),$)
    },
  )
$ <eq:possiblyinfinite>

but this morphism is not necessarily unique. However, there is a canonical choice $tr^infinity_c$ among these morphisms, namely the one which is maximal with respect to inclusion. We call this function $tr^infinity_c : X -> cal(P)(Z)$ the _possibly-infinite_ behavior for $c$.

Indeed, if we consider our running example LTS with termination,
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
$xi: Sigma^infinity -> 1 + Sigma times Sigma^infinity$ is the final $F$-coalgebra. Defined by $xi(epsilon)& =* in 1$ and $xi(sigma w)&= (sigma,w)$. Instantiating the diagram in @eq:possiblyinfinite, we obtain
$
  epsilon in tr_c (x) <==> x -> checkmark \
  sigma w in tr_c (x) <==> exists y. (x ->^sigma y and w in tr_c (y)).
$ <eq:infinite>

Which is the same as in @eq:finite. However, because the domain is $Sigma^infinity$, we obtain different words when we take the maximal function satisfying these equations. Namely the finite words, in addition to the infinite ones! For the system in @img:nd we get the same words as before, but additionally ${a b^infinity, a c^infinity} subset.eq tr^infinity_c (x_0)$. Interestingly, taking the minimum morphism we again obtain just the finite words @hasuo2007generic@jacobs2004trace.

== Coalgebraic Representation Büchi Automata <results:buchi>
We can apply the previous framework for possibly infinite words to our initial exmample for a Büchi automaton, in @img:buchi. This would yield all infinite words through automaton: $(mono("request") dot mono("process")^infinity dot mono("return"))^omega$. This is not quite the desired outcome yet, because $mono("process")^infinity$ means it takes the $mono("process")$ transition zero, some finite number, or an infinite number of times. How do we eliminate those words that process indefinitely? I.e. only accept those words under the Büchi acceptance criterion of passing through an accepting state infinitely many times.

A way of solving this is given by @urabe2016coalgebraic. In short, the main idea of their paper is to divide the states into accepting and non-accepting states. Then, applying the previous construction using the final $F$-coalgebra in *Sets* we obtain two separate commuting diagrams for these disjoint sets of states. And finally, using greatest and least fixed points we can precisely pick exactly the accepting words for the Büchi automaton.

We first give the commuting diagrams which govern the behavior mappings. We are now considering Büchi automata, so the functor we consider is $F X = Sigma times X$, the final coalgebra for this functor is $d: Sigma^omega -> Sigma times Sigma^omega$, defined by $d(sigma dot w) = (sigma,w)$, and the monad is still $cal(P)$. The lifting $overline(F)$ is effectively the same, just without a case for $*in 1$. We now consider the state space as a disjoint union $X=X_1 union X_2$ of non-accepting and accepting states, respectively. This gives rise to two separate coalgebras $c_i: X_i -> overline(F)X$, defined by the restriction $c compose kappa_i : X_i -> overline(F)X $ along the coprojection $kappa_i : X_i arrow.r.hook X$ for $i in {1,2}$. We then get the two commuting diagrams:

$
  #diagram(
    spacing: 1.1cm,
    {
      node((0, 0), [$Sigma times X$], name: <fx1>)
      node((0, 1), [$X_1$], name: <x1>)
      node((1, 1), [$Sigma^omega$], name: <z1>)
      node((1, 0), [$Sigma times Sigma^omega$], name: <fz1>)
      edge(<x1>, <fx1>, $c_1$, "->", left)
      edge(<x1>, <z1>, $tr_1$, "~>", right)
      edge(<fx1>, <fz1>, $Sigma times [tr_1,tr_2]$, "~>")
      edge(<z1>, <fz1>, $J d$, "->")
      edge(<z1>, <fz1>, $tilde.equiv$, "-", left, stroke: 0pt)

      node((2, 0), [$Sigma times X$], name: <fx2>)
      node((2, 1), [$X_2$], name: <x2>)
      node((3, 1), [$Sigma^omega$], name: <z2>)
      node((3, 0), [$Sigma times Sigma^omega$], name: <fz2>)
      edge(<x2>, <fx2>, $c_2$, "->", left)
      edge(<x2>, <z2>, $tr_2$, "~>", right)
      edge(<fx2>, <fz2>, $Sigma times [tr_1,tr_2]$, "~>")
      edge(<z2>, <fz2>, $J d$, "->")
      edge(<z2>, <fz2>, $tilde.equiv$, "-", left, stroke: 0pt)

      node((0.5,0.5), [$=_mu$])
      node((2.5,0.5), [$=_nu$])

      node((3.75, .5), $italic("in") cal("Kl")(cal(P)).$)
    },
  )
$ <eq:diagram>

// What the $=_mu$ and $=_nu$ in the center of the diagrams mean we will see later.
Where $=_mu$ and $=_nu$ mean that we take the lfp behavior mapping in the left diagram to obtain $beh_1$, and the gfp in the right diagram to obtain $beh_2$. More concretely, $beh_1: X_1 -> cal(P)(Sigma^omega)$ and $beh_2: X_2 -> cal(P)(Sigma^omega)$, are the solutions to the following system of equations:

// Spelling out the paths within the diagram we obtain that our behavior mapping $tr_1: X_1 -> cal(P)(Sigma^omega)$, $tr_2: X_2 -> cal(P)(Sigma^omega)$ must conform to the following equations.

$
  u_1 &=_mu (J d)^(-1) dot.circle overline(F)[u_1,u_2] dot.circle c_1 \
  u_2 &=_nu (J d)^(-1) dot.circle overline(F)[u_1,u_2] dot.circle c_2
$ <eq:traces>

#line(length: 100%)

#lemma(numbering: "1")[
  The traces
  $
    u_1 &=^mu (J d)^(-1) dot.circle overline(F)[u_1,u_2] dot.circle c_1 #h(3em)
    u_2 &=^nu (J d)^(-1) dot.circle overline(F)[u_1,u_2] dot.circle c_2
  $ //<eq:traces>

  coincide with:

  $
    u_1 =^mu diamond_delta ([u_1, u_2]) harpoon.tr X_1 #h(3em) u_2 =^nu diamond_delta ([u_1,u_2]) harpoon.tr X_2
  $

  Where $diamond_delta: (cal(P)(Sigma^omega))^(X)->(cal(P)(Sigma^omega))^(X)$ is given by
  $
    diamond_delta (beh)(x) = {sigma dot w | x'in delta(x)(sigma) , w in beh(x')}.
  $ <eq:diamond>
] <lemma:0>

#proof[
  First we unfold some definitions:

  $(J d)^(-1)= J (d^(-1))$ and $d^(-1)=cons$ and $J=eta_(Sigma^omega)$, so $J compose d^(-1) = eta_(Sigma^omega) compose cons$.

  $overline(F)[u_1,dots,u_n]= lambda_(Sigma^omega) compose (id times (u_1 + dots + u_n))$ so let us call $u_1+dots+ u_n=beh$ and see that $id times beh: (Sigma times X) -> (Sigma times cal(P)(Sigma^omega))$, maps a pair $(sigma,x)$ to $(sigma,beh(x))$, i.e. $sigma$ and the language accepted by $x$. Combining with the natural transformation $lambda: (Sigma times cal(P(Sigma^omega)))-> cal(P)(Sigma times Sigma^omega)$ defined by $lambda(sigma,W)={(sigma,w)| w in W }$ we get $overline(F)[u_1,dots,u_n](sigma,x)={(sigma,w) | w in beh(x)}$

  $c_i= c compose kappa_i: X_i -> cal(P)(Sigma times X)$ in terms of the automaton is defined as $c_(i)(x)={(sigma,x')| x' in X, sigma in Sigma, x' in delta(x)(sigma)}$ for $x in X_i$.

  Combining these, and writing out the Kleisli composition in terms of functions in *Sets* we get:

  $
    (J d)^(-1) dot.circle overline(F)[u_1,dots,u_n] dot.circle c_i = mu_(Sigma^omega) compose cal(P)(eta_(Sigma^omega) compose cons) compose (mu_(Sigma times Sigma^omega) compose cal(P)(lambda compose (id times (u_1 + dots + u_n))) compose c_i).
  $

  Observing that $mu_(Sigma^omega) compose cal(P)(eta_(Sigma^omega) compose cons) = cal(P(cons))$, letting $u_1+dots+u_n=beh$ again and combining $cal(P)(lambda compose (id times beh))$ and $c_1$ by using our observations from above we obtain, for an $x in X_i$:

  $
    (mu_(Sigma^omega) compose cal(P)(eta_(Sigma^omega) compose cons) compose (mu_(Sigma times Sigma^omega) compose cal(P)(lambda compose (id times (u_1 + dots + u_n))) compose c_1))(x) \
    = cal(P)(cons)({(sigma,w) | x' in X, x' in delta(x)(sigma), w in [u_1,dots,u_n](x') })\
    = {sigma dot w | x' in delta(x)(sigma), w in beh(x') } = diamond_delta (beh)(x)
  $

]
#line()

By taking exactly those behavior mappings which are the solution to this system of equation, we take exactly those words that the Büchi automaton accepts. The proof that this works is mostly done in the following two lemmas.


// $Run_chi$ is a (possibly infinite) run in the NFA $chi=(X=X_1union X_2, Sigma, delta, s)$. Meaning: $(sigma_1,x_1)(sigma_2,x_2) in Run_chi$ if $x_(i+1) in delta(x_i)(sigma_1)$ for $x_i,x_(i+1) in X$ and $sigma in Sigma$. $AccRun_(chi,X_i)$ are the accepting runs in $chi$ which start in $X_i$. asdf

#lemma([#cite(<urabe2016coalgebraic>, supplement: "Lemma 4.4")])[
  Let $chi=((X_1,X_2), Sigma, delta, s)$ be a Büchi automaton. Let $l^sol_1, l^sol_2$ be the solutions to the following equational system, where the variables $u_1,u_2$ range over $cal(P)(Run_chi)$


  $ u_1 =^mu diamond_chi^1 (u_1 union u_2) #h(3em) u_2 =^nu diamond_chi^2 (u_1 union u_2) $ <eq:runs>

  Here: $diamond_chi^i : cal(P)(Run_chi) -> cal(P)(Run_(chi,X_i))$ is given by $diamond_chi^i R := {(sigma,x)dot rho  | sigma in Sigma,  x in X_i, rho=(sigma_1,x_1)(sigma_2,x_2)... in R, x_1 in delta(x,sigma)}.$ Then $l^sol_1=AccRun_(chi,X_1),l^sol_2=AccRun_(chi,X_2). $
] <lemma:4.4>

A formal proof is found in @appendix, but we can use the intuition from @sec:modal to gain an understanding as to why this lemma holds. Namely the fact that the $mu$ operator is for finite looping, it has to have some endpoint or exit out of the loop, and that $nu$ is for infinite looping. So the second equation makes sure the run passes through $X_2$ infinitely many times. Note that it can still move through $X_1$, but it has to move through $X_2$ infinitely many times. The first equation, with the $mu$ operator, makes sure that any run passing through $X_1$ passes to the second equation in some finite number of steps, where it passes through $X_2$ infinitely many times.

Note that this is where we think a game semantic view could be applied. We think we might be able to define an intuitive correspondence between taking transitions in the Büchi automaton and the runs 'passing' through the equations in @lemma:4.4, and use that to characterize a game to decide which words belong to $"Lang"(chi)$.

Of course @lemma:4.4 worked with Runs, instead of actual words. The next lemma is closer to our desired result:

#lemma([#cite(<urabe2016coalgebraic>, supplement: "Lemma 4.5")])[
  Let $chi=((X_1,X_2), Sigma, delta, s)$ be a Büchi automaton. Let $l^sol_1, l^sol_2$ be the solutions to the following equational system, where the variables $u_1,u_2$ range over $(cal(P)(Sigma^omega))^(X_i)$

  $ u_1 =^mu diamond_delta^1 (u_1 union u_2) #h(3em) u_2 =^nu diamond_delta^2 (u_1 union u_2) $

  Where $diamond^i_delta: (cal(P)(Sigma^omega))^(X)->(cal(P)(Sigma^omega))^(X_i)$ is given by
  $
    diamond^i_delta (tr)(x) = {sigma dot w | sigma in Sigma, x'in delta(x)(sigma) , w in tr(x')}.
  $ <eq:diamond>
  Then the solutions $l^sol_i  = DelSt (AccRun_(chi,X_i))$, i.e. the words accepted starting from $X_i$.
] <lemma:4.5>

After observing that @eq:traces in fact coincides with the definition of $diamond_delta$, we obtain the final theorem:

#theorem([#cite(<urabe2016coalgebraic>, supplement: "Theorem 4.6")])[
  Let $chi=((X_1,X_2), Sigma, delta, s)$ be a Büchi automaton. Then the behavior mappings $tr_1,tr_2$, which are the solution to the system of equations in @eq:traces coincide with the accepted language of $chi$: $tr(chi)=[tr_1,tr_2] dot.circle s (*) = "Lang"(chi)$. Where we interpret $s subset.eq X$ as $s: 1 -> cal(P)(X)$.
] <th>

= Derivation of Coincidence Using Game Semantics
In this section we prove @th using game semantics and in a very pretty way.

#definition[
  Let $A=(X_1 union X_2, Sigma, delta)$ be a Büchi automaton, with states $X=X_1 union X_2$ where $X_2$ are the accepting states, $Sigma$ is the alphabet, and $delta: X times Sigma -> cal(P)(X)$ the transition function. We define a Transition System (TS) over the set of propositional variables ${p_1,p_2}$ for this automaton, denoted as $T_A$, as follows:
  - States are $(x,w)$ for $x in X$ and $w in Sigma^omega$
  - Transition $(x,sigma w) -> (x', w)$ for $x,x'in X$, $sigma in Sigma$, $w in Sigma^omega$, iff $x'in delta(x)(sigma)$
  - Labeling function given by $lambda((x,w))={p_i}$ iff $x in X_i$, i.e. the propositional variables denote for what $i$, we have $x in X_i$.
]

We observe how the formulas from @lemma:0 are built up and convert them. For example the closed formula for $beh_1: X_1 -> Sigma^omega$ for $n=2$ priorities, i.e. a Büchi automaton, $beh_1=nu u_2. diamond_delta [mu u_1. [u_1,u_2] arrow.t X_1, u_2] arrow.t X_2$. Let $phi$ be such a formula, then:
- $phi=u$ a free variable, or
- $phi=diamond_delta phi'$, or
- $phi=eta u. phi'$ where $eta in {mu,nu}$, or
- $phi = phi' arrow.t X_i $, or
- $phi=[phi_1,dots,phi_n]$

we also observe the implicit semantics of the formula $||phi||$: ...

#definition[So we convert a formula $phi$, to our desired formula $overline(phi)$ to conform to Definition 10.2[]:
  - $phi=u$ a free variable then $overline(phi)=u$ also a free variable
  - $phi=diamond_delta phi'$ then $overline(phi)=diamond overline(phi')$
  - $phi=eta u. phi'$ for $eta in {mu,nu}$ then $overline(phi)=eta u . overline(phi')$
  - $phi = phi' arrow.t X_i $ then $overline(phi)=p_i and overline(phi')$
  - $phi=[phi_1,dots,phi_n]$ then $overline(phi)=(p_1 and overline(phi_1)) or ... or (p_n and overline(phi_n))$
]


#lemma()[
  For a modal $mu$-calculus formula $phi$ (a la paper 1) and a valuation $V: Var -> (X -> cal(P)(Sigma^omega))$, $x in X, w in Sigma^omega$:

  $
    w in ||phi||_(V) (x) <=> (x,w) in ||overline(phi)||^(T_A)_overline(V)
  $

  where $overline(V)(U)={(x,w)| x in X, w in V(U)(x)}$
]
#let ubar = $overline(U)$
#let vbar = $overline(V)$
#let wbar = $overline(W)$
#let ybar = $overline(Y)$
#let dd = $diamond_delta$
#proof[
  We prove this by induction on the formula $phi$. The base case is $phi=U$ a free variable:

  $w in ||U||_(V)(x)=V(U)(x) <-> (x,w) in overline(V)(U) = ||U||^(T_A)_(overline(V))$

  Induction step:

  - $phi=mu U. phi'$:

  We have to show $w in ||mu U. phi'||_(V)(x)=lfp(lambda u. ||phi'||_(V[U |-> u])) <=> (x,w) in ||mu U. overline(phi')||_(overline(V))=lfp (lambda u. ||overline(phi')||_(overline(V)[U |-> u]))$. Let $W= lfp(lambda u. ||phi'||_(V[U |-> u]))$. We define $overline(W)={(x,w) | x in X, w in W(x)}$ and show $W= lfp(lambda u. ||phi'||_(V[U |-> u]))<=>overline(W)= lfp(lambda u. ||overline(phi')||_(V[U |-> u]))$. For this we first prove that $W$ is a fixed point iff $overline(W)$ is a fixed point:

  Assume $W$ is a fixed point, so $||phi'||_(V[U |-> W]) = W$. We observe that for a valuation $V$ and $V'$ where $V'=V[U|->W]$, we have the converted valuation $overline(V')=overline(V)[U |-> overline(W)]$. We use this to incite the IH to get $w in ||phi'||_(V[U|->W]) <=> (x,w) in ||overline(phi')||_(overline(V)[U |-> overline(W)])$. Using this we get $(x,w) in ||overline(phi')||_(overline(V)[U|-> overline(W)]) <=> w in ||phi'||_(V[U |-> W])(x)=W(x) <=> (x,w) in overline(W)$, so $||overline(phi')||_(overline(V)[U |->overline(W)])= wbar$, so $wbar$ is a fixed point.

  Now assume $overline(W)$ is a fixed point, so $||overline(phi')||_(overline(V)[U |-> wbar]) = wbar$. Then, for $x in X$, $W(x)={w | (x,w) in overline(W)}$. Applying IH like the previous case again we obtain $w in ||phi'||_(V[U |-> W])(x) <=> (w,x) in ||overline(phi')||_(overline(V)[U |-> overline(W)])= W <=> w in W(x) $. So $w in ||phi'||_(V[U |-> W])(x) <=> w in W(x)$ for all $x in X$, so $||phi'||_(V[U |-> W])=W$, so $W$ is a fixed point.

  Next, we show that $W$ is the _least_ fixed point iff $overline(W)$ is the _least_ fixed point:

  Assume $W$ is a lfp, from above we know that $wbar$ is a fixed point. Take some other fixed point $ybar$, i.e. $||overline(phi')||_(overline(V)[U|->ybar])=ybar$. Now, again inciting what we showed above, we know $Y$ is a fixed point, so $||phi'||_(V[U|->ybar])=ybar$. So because $W$ is the lfp, for all $x$, $W(x)subset.eq Y(x)$. From this it follows that $(x,w) in wbar -> w in W(x) -> w in Y(x) -> (x,w) in ybar$, so $wbar subset.eq ybar$. So $wbar$ is the least fixed point.

  For the other direction, assume $overline(W)$ is a least fixed point. Then $W$ is a fixed point. Take some other fixed point $Y$, i.e. $||phi'||_(V[U|->Y])=Y$, then $ybar$ is a fixed point. So because $wbar$ is the lfp, we have $wbar subset.eq ybar$. Now for any $w,x$ we have $w in W(x) -> (x,w) in wbar -> (x,w) in ybar -> w in Y(x)$. So $W subset.eq Y$.

  - $phi=nu U. phi'$:

  This case is a analagous to the $mu$ case. The first part proving $W$ is a fixed point iff $wbar$ is a fixed point, and for proving $W$ is a _greatest_ fixed point iff $wbar$ is too you reason in the opposite direction as for $mu$.

  - $phi=diamond_delta phi'$: \
  $w in & ||diamond_delta phi'||_(V)(x)
    = {sigma w | exists x' in delta(x)(sigma)[ w in ||phi'||_(V)(x')] }
    =^(I H){sigma w | exists x' in delta(x)(sigma)[ (x',w) in ||phi'||_(overline(V))] }
    <-> (x,w) in {(x,sigma w) | exists x' in delta(x)(sigma)[ (x',w) in ||phi'||_(overline(V))] }
    = ||diamond overline(phi')||^(T_A)_(overline(V))$
  - $phi = phi' harpoon.tr X_i$: \
  $w in ||phi' harpoon.tr X_i||_(V)(x) <-> x in X_i and w in ||phi'||_(V)(x) <->^(I H)x in X_i and (x,w) in ||overline(phi')||_(overline(V)) <-> (x,w) in ||p_i and overline(phi')||_(overline(V))$
  - $phi= [phi_1,dots,phi_n]$:
  $||phi||_(V)(x) = cases(||phi_1||_(V)(x) "if " x in X_1, dots.v, ||phi_n||_(V)(x) "if " x in X_n)$, so let $w in ||phi||_(V)(x)$ for $x in X_i$, then $w in ||phi_i||_(V)(x)$ so by IH $(x,w) in ||overline(phi_i)||_(overline(V))(x)$, and because $x in X_i$, $(x,w) in X_i$, $(x,w) in ||p_i and overline(phi_i)||_(overline(V))(x)$ and thus $(x,w) in ||(p_1 and phi_1) or ... or (p_n and phi_n)||_overline(V)=||overline(phi)||_overline(V)$.

  Now $(x,w) in ||overline(phi)||_overline(V) = ||(p_1 and overline(phi_1)) or ... or (p_n and overline(phi_n))||_overline(V)$. Take $i$ such that $(x,w) in ||p_i and overline(phi_i)||_overline(V)$ then we have $x in X_i$ and (by IH) $w in ||phi_i||_(V)(x)$, and by definition of $||[phi_1,...,phi_n]||$ then $w in ||phi||_(V)(x)$.
]



= Conclusion and Future Work <sec:conclusion>
In this report we have shown a coalgebraic representation of Büchi automata. The construction relies upon two key ideas: working in the Kleisli category for the monad $cal(P)$ and deriving two separate commuting diagrams for the accepting and non-accepting states and obtaining the right words by utilizing fixed point equations from these two mappings.

We explained the model in the Kleisli category in @sec:nd by showing how to construct a final coalgebra for finite words for a nondeterministic system. Subsequently we constructed a weakly final coalgebra to additionally obtain the infinite words within such a system. Building upon these ideas we derived the coalgebraic construction for Büchi automata in @results:buchi, making use of the modal mu-calculus explained in @sec:modal.

We provided a proof for @lemma:4.4, but not for @lemma:4.5, which is crucial for coincidence result in @th, and thus understanding why the construction indeed provides the words accepted by the Büchi automaton. Therefore, the first next step in the internship will be understanding the proof provided by @urabe2016coalgebraic.

After understanding the full proof of the coincidence result, we can start to think about replacing it using a different framework. Our goal is to replace it using a game semantics framework, which we briefly explained in @sec:modal in relation to the modal mu-calculus. There, we showed how one can see the check whether a formula holds in a state as a two player game between a verifier and a refuter, who want to verify, respectively refute, that the formula holds. Our vision is that this view can be applied to whether a word is accepted by the coalgebraic model of a Büchi automaton, and that this could simplify the result.

#bibliography("refs.bib", style: "association-for-computing-machinery")

#show: appendix

= Proofs <appendix>
_Proof of @lemma:4.4 _:
We prove this in three steps: we show some properties for the first intermediate solution $l^((1))_1$, subsequently we use that to show $l^sol_2 = AccRun_(chi,X_2)$, and finally we use both results to show $l^sol_1 = AccRun_(chi,X_1)$.

Let $|rho|$ denote the length of the run $rho$.

Let $k in omega$, $u_2 in cal(P)(Run_(chi,X_2))$, and any (possibly infinite) run $rho=(sigma_1,x_1)(sigma_2,x_2)dots in Run_chi$,

$ rho in [lambda u_1. diamond^1_chi (u_1 union u_2)]^k (emptyset) $ <l11>

if and only if
// 1. For all $i<= |rho|$, $x_i in X_1$. Moreover, $|rho| <= k$, so the run is finite.
there exists an $i <= k$, such that for all $j <= i$ we have $x_j in X_1$ and $(sigma_(i+1),x_(i+1))(sigma_(i+2),x_(i+2))... in u_2$. Meaning, for $i$ steps the run passes through $X_1$ and after that it moves into $u_2$.

This is the case because when applying the function on $k$ times there occur at most $k$ steps in $X_1$ due to the $diamond$ operator. After this the run has to move into $u_2$. The other direction is obvious.

Now we observe that
$
  l^((1))_1 (u_2) = mu u_1. diamond^1_chi (u_1 union u_2)= union.big_(k in omega) [ lambda u_1. diamond^1_chi (u_1 union u_2) ]^k (emptyset)
$

So $rho in mu u_1.diamond^1_chi (u_1 union u_2)$ if and only if the run $rho$ moves after some finite number of steps into $u_2$.

Now for $k in omega$, and a (possibly infinite) run $rho=(sigma_1,x_1)(sigma_2,x_2)dots in Run_chi$,

$ rho in [lambda u_2. diamond^2_chi (l^((1))_1(u_2) union u_2)]^k (Run_(chi,X_2)). $

if and only $|{i | x_i in X_2}|>= k$, i.e. we have passed through $X_2$ at least $k$ times.

This is because, again, we take some number of steps in $X_2$ due to the $diamond$ operator, and between these steps we can 'pass through' $l^((1))_1$ but then, as shown above, the run has to move back to $X_2$.

Analogous to the least fixed point, we now observe that

$
  l^sol_2 = nu u_2. diamond^2_chi (l^((1))_1(u_2) union u_2) = sect.big_(k in omega) [ lambda u_2.
    diamond^2_chi (l^((1))_1(u_2) union u_2) ]^k (Run_(chi,X_2)).
$

So $rho in nu u_2. diamond^2_chi (l^((1))_1(u_2) union u_2)$ if and only if for all $k$ $rho$ has moved through $X_2$ at least $k$ times. Meaning, $rho$ has passed through $X_2$ infinitely many times. So $l^sol_2 = AccRun_(chi,X_2)$.

Finally,

$ l^(sol)_1 = l^((1))_1(l^(sol)_2). $

So for $rho in l^(sol)_1$, in finitely many steps the run moves to $l^sol_2$, for which it passes infinitely many times through $X_2$. So $l^(sol)_1=AccRun_(chi,X_1)$. #h(1fr) $square$
