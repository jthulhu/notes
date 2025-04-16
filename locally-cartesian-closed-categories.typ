#import "@preview/ctheorems:1.1.3": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
#import "@preview/cetz:0.3.4"
#import cetz.draw
#set text(font: "New Computer Modern")
#set document(title: [Notes on Fibrations], author: "Adrien Mathieu")
#set heading(numbering: "1.")
#show: thmrules.with(qed-symbol: $square$)

#let definition = thmbox("all", "Definition", inset: (top: .5em))
#let theorem = thmbox("all", "Theorem", inset: (top: .5em))
#let lemma = thmbox("all", "Lemma", inset: (top: .5em))
#let proof = thmproof("proof", "Proof")

#v(20%)
#align(center, text(25pt)[*Notes on LCCC*])
#align(center, text(15pt)[Adrien #smallcaps([Mathieu])])
#v(10%)
#outline()
#pagebreak()

#set page(
    footer: align(
        center,
        context counter(page).display("-- 1 --"),
    ) ,
)
#counter(page).update(1)

= Introduction

== Preliminary notions

=== Change of base functor

For this section, assume that we have a category $cal(C)$ which has pullbacks.  Let $X, Y$ be two
objects in $cal(C)$, and $f : X arrow Y$.  We can build $ f^* : cal(C) "/" Y arrow.long cal(C) "/" X $
the "base change" functor as follows: let $g : Z arrow Y$ be an element of $cal(C) "/" Y$.

#align(center, diagram(spacing: 2cm, $
    X times_Y Z edge("d", f^*(g), ->) edge(->)
        & Z edge("d", g, ->) \
    X edge(f, ->) & Y
$,
    edge(
        (.3, .3),
        (0, 0),
        stroke: white,
        marks: (
            (inherit: "straight", sharpness: 45deg, size: 18, pos: .5, stroke: black),
        ),
    )
))

Furthermore, if $h : W arrow Y$ is an other element of $cal(C) "/" Y$ and $phi : h arrow g$, by
pullback, there exists a unique $f^*(phi) : X times_Y W arrow X times_Y Z$ making the following
diagram commute
#align(center, diagram(spacing: (.5cm, 1cm), $
    & & X times_Y W edge("rrr", ->) edge("dll", ->, f^*(phi), "dashed")
    edge("dddl", ->, f^*(h), label-pos: #60%, label-side: #left)
        & & & W edge("dddl", h, ->) edge("dll", phi, ->) \
    X times_Y Z edge("ddr", f^*(g), ->, label-side: #right) edge("rrr", ->, crossing: #true)
        & & & Z edge("ddr", g, ->) \ \
        & X edge("rrr", f, ->) & & & Y
$,
    edge(
        (.5, 1.3),
        (0, 1),
        stroke: white,
        marks: (
            (inherit: "straight", sharpness: 30deg, size: 18, pos: .5, stroke: black),
        ),
    ),
    edge(
        (2.35, 0.39),
        (2, 0),
        stroke: white,
        marks: (
            (inherit: "straight", sharpness: 60deg, size: 18, pos: .2, stroke: black),
        ),
    ),
))
hence, $f^*(phi)$ is a morphism $f^*(h) arrow.long f^*(g)$.

#lemma[$f^*$ defines a functor.]

#proof[
    Let $(Z, g) : cal(C) "/" Y$.  Note that the following diagram commutes
    #align(center, diagram(spacing: (.5cm, 1cm), $
        & & X times_Y Z edge("rrr", ->) edge("dll", ->, id_(f^*(g)))
        edge("dddl", ->, f^*(g), label-pos: #60%, label-side: #left)
            & & & Z edge("dddl", g, ->) edge("dll", id_g, ->) \
            X times_Y Z edge("ddr", f^*(g), ->, label-side: #right) edge("rrr", ->, crossing: #true)
            & & & Z edge("ddr", g, ->) \ \
            & X edge("rrr", f, ->) & & & Y
    $,
        edge(
            (.5, 1.3),
            (0, 1),
            stroke: white,
            marks: (
                (inherit: "straight", sharpness: 30deg, size: 18, pos: .5, stroke: black),
            ),
        ),
        edge(
            (2.35, 0.39),
            (2, 0),
            stroke: white,
            marks: (
                (inherit: "straight", sharpness: 60deg, size: 18, pos: .2, stroke: black),
            ),
        ),
    ))
    thus $id_(f^*(g))$ satisfies the universaly property of $f^*(id_g)$, and so $
        f^*(id_g) = id_(f^*(g))
    $

    Let $(U, h), (V, j) : cal(C) "/" Y$, $phi : (Z, g) arrow (U, h)$ and $psi : (U, h) arrow (V, j)$.
    #align(center, diagram(spacing: (.5cm, 1cm), $
        & & & & X times_Y Z edge("rrr", ->) edge("dll", ->, f^*(phi))
        edge("ddddlll", ->, f^*(g), bend: #10deg, label-pos: #65%)
            & & & Z edge("dll", ->, phi) edge("ddddlll", ->, g, bend: #10deg)\
        & & X times_Y U edge("rrr", ->, crossing: #true) edge("dll", ->, f^*(psi))
        edge("dddl", ->, f^*(h), label-pos: #60%, label-side: #left)
            & & & U edge("dddl", h, ->) edge("dll", psi, ->) \
            X times_Y V edge("ddr", f^*(j), ->, label-side: #right) edge("rrr", ->, crossing: #true)
            & & & V edge("ddr", j, ->) \ \
            & X edge("rrr", f, ->) & & & Y
    $))
    Note that the topmost outer rectangle commutes because both inner square commute, and that the
    leftmost, outermost triangle commutes too because both inner triangle commute, making
    $f^*(psi) compose f^*(phi)$ satisfy the same universal condition as $f^*(psi compose phi)$, so $
        f^*(phi compose phi) = f^*(psi) compose f^*(phi)
    $
]

== Main theorem

#definition([Locally Cartesian Closed Category])[
    A category $cal(C)$ is _locally cartesian closed_ if, for any object $X : cal(C)$, the
    category $cal(C) "/" X$ is cartesian closed.
]

#theorem[
    A category $cal(C)$ is locally cartesian closed if, and only if, it has
    - pullbacks;
    - for any morphism $f : X arrow Y$ in $cal(C)$, the functor $f^*$ has a right adjoint $Pi_f$,
      called the _dependent product at $f$_.
]

= The direct part of the equivalence
Suppose we have a locally cartesian closed category $cal(C)$.

== Pullbacks
Let's show that $cal(C)$ has pullbacks.  Let $f, g$ be morphisms in $cal(C)$ spelling out
the following diagram
#align(center, diagram(spacing: 2cm, $
    & Y edge("d", g, ->) \
    X edge(f, ->) & Z
$))
Since $cal(C) "/" Z$ is cartesian closed, there exists a $(X times_Z Y, h) : cal(C) "/" Z$
the cartesian product of $(X, f)$ and $(Y, g)$, with projections $pi_1$ and $pi_2$:
#align(center, diagram(spacing: 2cm, $
    X times_Z Y edge("d", pi_1, ->) edge(pi_2, ->)
    edge("dr", h, ->)
        & Y edge("d", g, ->) \
    X edge(f, ->) & Z
$))
This latter square (if we forget about $h$) is a pullback.  Indeed, for any $U : cal(C)$,
$i : U arrow X$ and $j : U arrow Y$ making the following diagram commute
#align(center, diagram(spacing: 2cm, $
    U edge("drr", j, ->, bend: #20deg) edge("ddr", i, ->, bend: #(-20deg)) \
        & X times_Z Y edge("d", pi_1, ->) edge(pi_2, ->)
        & Y edge("d", g, ->) \
        & X edge(f, ->) & Z
$))
Let $h' = g compose j = f compose i$.  Note that $j : (U, h') arrow (Y, g)$ and
$i : (U, h') arrow (X, f)$ in $cal(C) "/" Z$, so by cartesianity, there exists a unique
$phi : (U, h') arrow (X times_Z Y, h)$ such that $pi_2 compose phi = j$ and
$pi_1 compose psi = i$, that is, the following diagram commutes
#align(center, diagram(spacing: 2cm, $
    U edge("drr", j, ->, bend: #20deg) edge("ddr", i, ->, bend: #(-20deg))
    edge("dr", phi, ->, "dashed") \
        & X times_Z Y edge("d", pi_1, ->) edge(pi_2, ->)
        & Y edge("d", g, ->) \
        & X edge(f, ->) & Z
$))
Note that any $phi$ making the two triangles commute is also a morphism $(U, h') arrow (X times_Z Y, h)$
in $cal(C) "/" Z$, so $phi$ is indeed unique in $cal(C)$.

== Dependent product
=== Definition
Let $f : X arrow Y$ be a morphism in $cal(C)$, let us define the functor $
    Pi_f : cal(C) "/" X arrow.long cal(C) "/" Y
$
Consider a $(Z, p) : cal(C) "/" X$.

=== Adjunction
// Local Variables:
// tp--master-file: "./locally-cartesian-closed-categories.typ"
// End:
