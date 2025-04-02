#import "@preview/ctheorems:1.1.3": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
#set text(font: "New Computer Modern")
#set document(title: [Notes on Fibrations], author: "Adrien Mathieu")
#set heading(numbering: "1.")
#show: thmrules.with(qed-symbol: $square$)

#let definition = thmbox("definition", "Definition", inset: (top: .5em))
#let theorem = thmbox("theorem", "Theorem", inset: (top: .5em))
#let lemma = thmbox("lemma", "Lemma", inset: (top: .5em))
#let proof = thmproof("proof", "Proof")
#let Cat = [*Cat*]
#let Fib(C) = $#[*Fib*]_(#C)$
#let Pfct(C) = $#[*Pfct*]_(#C)$
#v(20%)
#align(center, text(25pt)[*Notes on Grothendieck Fibrations*])
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

== Preliminary definitions

In this section, we have two categories $cal(B)$ and $cal(E)$, and a functor $p : cal(E) arrow
cal(B)$.
#definition("Refinement")[
    Let $R : cal(E)$ and $X : cal(B)$.  We say that _$R$ refines $X$_, or $R subset.sq X$, if $ X = p(R) $
]

We note #diagram($R edge("-[]") & X$) to mean $R subset.sq X$, and we say that the following diagram commutes
#align(center)[#diagram(spacing: 2cm, $
    S edge("d", "-[]") edge(alpha, ->) & R edge("d", "-[]") \
    X edge(f, ->) & Y
$)]
if $f = p(alpha)$.

#definition("Cartesian morphism")[
    Let $R, S : cal(E)$.  A morphism $alpha : S arrow R$ is _cartesian_ if, for any
    $S' : cal(E)$, $alpha' : S' arrow R$, and $f : p(S') arrow p(S)$ such that the following diagram
    commutes
    #align(center)[#diagram(spacing: 2cm, $
        p(S') edge(p(alpha'), ->) edge("d", f, ->) & p(R) \
        p(S) edge("ur", p(alpha), ->)
    $)]
    There exists a unique $hat(f) : S' arrow S$ such that $f = p(hat(f))$, and such that the following
    diagram commutes
    #align(center)[#diagram(spacing: 2cm, $
        S' edge(alpha', ->) edge("d", hat(f), ->, "dashed") & R \
        S edge("ur", alpha, ->)
    $)]
]

#lemma()[
    A cartesian morphism is an isomorphism.
]<cartesian-iso>
#proof()[
    Let $R,S : cal(E)$ and $alpha : R arrow S$ be a cartesian morphism in $cal(E)$.
]

#definition("Fibration")[
    $p$ is said to be a _fibration_ if, for any
    #align(center)[#diagram(spacing: 2cm, $
        & R edge("d", "-[]") \
        X edge(f, ->) & Y
    $)]
    there exists a cartesion morphism $alpha$ making the following commute
    #align(center)[#diagram(spacing: 2cm, $
        S edge(alpha, ->) edge("d", "-[]") & R edge("d", "-[]") \
        X edge(f, ->) & Y
    $)]
]

#definition([Category of fibrations])[
    For a base category $cal(B)$, define $Fib(cal(B))$ as the category of fibrations over
    $cal(B)$, that is, whose objects are pairs $(cal(E), p)$ with $cal(E)$ a category and
    $p : cal(E) arrow cal(B)$ a fibration.

    Given two fibrations $p_i : cal(E)_i arrow cal(B)$ over $cal(B)$ for $i=1,2$, a morphism of
    fibrations between $p_1$ and $p_2$ is a functor $F : cal(E)_1 arrow cal(E)_2$ making the
    following diagram commute
    #align(center)[#diagram(spacing: 2cm, $
        cal(E)_1 edge(F, ->) edge("d", p_1, ->) & cal(E)_2 edge("d", p_2, ->) \
        cal(B) edge(id_(cal(B)), ->) & cal(B)
    $)]
    and which preserves cartesianity of morphisms.
]

#definition([Category of pseudofunctors])[
    For a given base category $cal(B)$, define $Pfct(cal(B))$ as the category whose elements
    are contravariant pseudo-functors $cal(P) : cal(B)^(op) arrow Cat$ in $Cat$, that is,
    - #box(width: 100%)[for each object $X : cal(B)$, a category $cal(P)_X$;]
    - for each morphism $f : X arrow Y$ in $cal(B)$, a functor $cal(P)_f : cal(P)_Y arrow cal(P)_X$;
    - for each object $X : cal(B)$, a natural isomorphism $
        i_X : cal(P)_(id_X) arrow.double.long id_(cal(P)_X)
    $
      called the pseudo unit of $cal(P)$ at $X$;
    - for each morphisms $f : X arrow Y$ and $g : Y arrow Z$ in $cal(B)$, a natural isomorphism $
        c_(f, g) : cal(P)_(g compose f) arrow.double.long cal(P)_f compose cal(P)_g
    $
      called the pseudo composition law of $cal(P)$ at $f$ and $g$.

    We additionally require the following coherence conditions: for $f : X arrow Y$, the following
    diagram commutes
    #align(center, diagram(spacing: 2cm, $
        cal(P)_f edge(c_(f, id_Y), ->) edge("d", c_(id_X, f), ->) edge("dr", id_cal(P)_f, ->)
            & cal(P)_f compose cal(P)_(id_Y) edge("d", cal(P)_f compose i_Y, ->, label-side: #left) \
            cal(P)_(id_X) compose cal(P)_f edge(i_X compose cal(P)_f, ->, label-side: #right) & cal(P)_f
    $))
    Furthermore, for $f : W arrow X$, $g : X arrow Y$ and $h : Y arrow Z$, the following diagram
    commutes
    #align(center, diagram(spacing: 2cm, $
        cal(P)_(h compose g compose f) edge(c_(f, h compose g), ->) edge("d", c_(g compose f, h), ->)
            & cal(P)_f compose cal(P)_(h compose g) edge("d", cal(P)_f compose c_(g, h), ->) \
            cal(P)_(g compose f) compose cal(P)_h edge(c_(f, g) compose cal(P)_h, ->)
            & cal(P)_f compose cal(P)_g compose cal(P)_h
    $))

    Given two pseudofunctors $cal(P)$ and $cal(P)'$, a morphism $nu : cal(P) arrow cal(P)'$ is a
    pseudonatural transformation between $cal(P)$ and $cal(P)'$, that is, for each point $X :
    cal(B)$, a functor $nu_X : cal(P)_X arrow cal(P)'_X$ and, for each morphism $f : X arrow Y$
    in $cal(B)$, a natural isomorphism
    #align(center)[#diagram(spacing: 2cm, $
        cal(P)_Y edge(nu_Y, ->) edge("d", cal(P)_f, ->)
            & cal(P)'_Y edge("d", cal(P)'_f, ->) edge("dl", nu_f, =>) \
        cal(P)_X edge(nu_X, ->) & cal(P)'_X
    $)]
    satisfying the following coherence conditions:
]

- for $X : cal(B)$, the following pasting is $nu_X$
  #align(center, diagram(spacing: 2cm, $
      cal(P)_X edge("d", cal(P)_(id_X), ->) edge(nu_X, ->)
      edge("d", id_(cal(P)_X), ->, bend: #(-90deg))
          & cal(P)'_X edge("d", cal(P)'_(id_X), ->) edge("dl", nu_(id_X), =>)
          edge("d", id_(cal(P)'_X), ->, bend: #90deg) \
          cal(P)_X edge(nu_X, ->) & cal(P)'_X
  $,
      edge((-.4, .5), (-.7, .5), $i_X$, "=>"),
      edge((1.7, .5), (1.04, .5), $i^(-1)_X$, "=>"),
  ))
  that is, $
      (nu_X compose i_X) compose nu_(id_X) compose (i'^(-1)_X compose nu_X) = id_(nu_X)
  $
- if $f : X arrow Y$ and $g : Y arrow Z$ are two morphisms in $cal(B)$, $nu_(g compose f)$ is
  obtained by pasting the squares (plus pseudo-composition)
  #align(center, diagram(spacing: 2cm, $
      cal(P)_Z edge(nu_Z, ->) edge("d", cal(P)_g, ->) edge("dd", cal(P)_(g compose f), ->, bend: #(-50deg))
          & cal(P)'_Z edge("d", cal(P)'_g, ->) edge("dl", nu_g, =>)
          edge("dd", cal(P)'_(g compose f), ->, bend: #50deg)\
          cal(P)_Y edge(nu_Y, ->) edge("d", cal(P)_f, ->)
          & cal(P)'_Y edge("d", cal(P)'_f, ->) edge("dl", nu_f, =>) \
          cal(P)_X edge(nu_X, ->) & cal(P)'_X
  $,
      edge((1.5, 1), (1, 1), $c'_(f, g)$, "=>"),
      edge((0, 1), (-.5, 1), $c^(-1)_(f, g)$, "=>")
  ))
  that is, $
      nu_(g compose f) = (nu_X compose c^(-1)_(f, g)) compose (nu_f compose cal(P)_g)
      compose (cal(P)'_f compose nu_g) compose (c'_(f,g) compose nu_Z)
  $


== Main theorem
We aim at proving the
#theorem([Main theorem])[
    For a given base category $cal(B)$, we have $ Fib(cal(B)) tilde.equiv Pfct(cal(B)) $
]

In order to do so, we will build in @fiber-functor half of the equivalence, namely, $ Phi :
Fib(cal(B)) arrow Pfct(cal(B)) $ and, in @grothendieck-construction, the other half of the
equivalence, namely, $ Psi : Pfct(cal(B)) arrow Fib(cal(B)) $

In @equivalence, we will show that the two form the two halves of an equivalence, finishing the
proof.
// Local Variables:
// tp--master-file: "/home/adri/dev/notes/notes.typ"
// End:
