#import "@preview/touying:0.6.1": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
#import "@preview/shadowed:0.2.0": shadowed
#import themes.university: *

#let colors = (
    primary: rgb("#0c4842"),
    bg-light: rgb(80%, 90%, 70%,),
    bg-gray: luma(230),
)

#let Fib = [*Fib*]

#set text(font: "New Computer Modern")
#show: university-theme.with(
    aspect-ratio: "4-3",
    config-common(
        new-section-slide-fn: none,
    ),
    primary: colors.primary,
    config-info(
        title: [Grothendieck construction],
        author: [Adrien #smallcaps([Mathieu])],
        date: datetime(
            year: 2025,
            month: 03,
            day: 24,
        ),
    ),
    config-colors(
        neutral-darkest: rgb("#000000"),
        neutral-dark: rgb("#202020"),
        neutral-light: rgb("#f3f3f3"),
        neutral-lightest: rgb("#ffffff"),
    ),
)
#set text(18pt)
#let diagram = touying-reducer.with(
    reduce: fletcher.diagram, cover: fletcher.hide
)
#title-slide()

#let myblock(title, content) = {
    let shadow-size = 5pt
    // show: body => shadowed(
    //     radius: shadow-size,
    //     inset: 0pt,
    //     dx: shadow-size,
    //     dy: shadow-size,
    //     body,
    // )
    block(
        fill: colors.bg-light,
        inset: 8pt,
        width: 100%,
        radius: (
            top: shadow-size,
        ),
    )[
        #set text(22pt)
        *#title*
    ]
    block(
        fill: colors.bg-gray,
        above: 0pt,
        inset: (
            left: 12pt,
            right: 5pt,
            top: 10pt,
            bottom: 15pt,
        ),
        width: 100%,
        radius: (
            bottom: shadow-size,
        ),
        content,
    )
}

#let definition(content) = myblock("Definition", content)
#let theorem(content) = myblock("Theorem", content)

= Fibration

#slide[]

== Refinement system
#slide[
    Assume that we have two categories $cal(B)$ and $cal(E)$, and a functor $p : cal(E) arrow cal(B)$.

   
    #definition[For $R : cal(E)$ and $X : cal(B)$, we say that $R$ _refines_ $X$, or $R subset.sq X$ if $ X =
    p(R) $]
    #pause
    #align(horizon, columns(2, {
        align(center + horizon, diagram(spacing: 3cm, $ R edge("d","-[]") \ X $))
        colbreak()
        pause
        align(center + horizon, diagram(spacing: 3cm, $ S edge(alpha, ->, label-side: #right) edge("d", "-[]") & R edge("d", "-[]") \ X edge(f, ->) & Y $))
    }))
]

== Cartesian morphism
#slide[
    #show: bd => align(horizon, bd)
    #definition[
        A morphism $alpha : S arrow R$ in $cal(E)$ is _cartesian_ when, for any morphism
        $beta : S' arrow R$ in $cal(E)$ and $g : p(S') arrow p(S)$ such that $
            p(beta) = p(alpha) compose g
        $
        there exists a unique lifting $gamma : S' arrow S$ of $g$ (ie $p(gamma) = g$) such
        that $
            beta = alpha compose gamma
        $
    ]
    #align(center, diagram(spacing: (3cm, 1cm), $
        S' edge("dd", "-[]") edge("drr", g, ->, bend: #20deg) edge("dr", gamma, ->, "dashed") \
            & S edge(alpha, ->) & R edge("dd", "-[]") \
            p(S') edge("dr", g, ->, label-side: #right) edge("drr", p(g), ->, bend: #20deg, label-pos: #70%) \
            & p(S) edge("uu", "[]-", crossing: #true) edge(p(alpha), ->, label-side: #right) & p(R)
    $))
]

== Fibration

#slide[
    #show: bd => align(horizon, bd)
    
    #definition[
        A functor $p : cal(E) arrow cal(B)$ is a _fibration_ if, for any $f : X arrow Y$ in
        $cal(B)$, and $R subset.sq Y$ #pause there exists a cartesian morphism
        $alpha : S arrow R$ above $f$ ($p(alpha) = f$).
        #meanwhile
        #align(center, diagram(spacing: 2cm, $
            & R edge("d", "-[]") \
            X edge(f, ->) & Y
        $,
            pause,
            node((0, 0), $S$),
            edge("d", "-[]"),
            edge($alpha$, "->"),
        ))
    ]
    #pause
    Given two fibrations $p : cal(E) arrow cal(B)$ and $q : cal(F) arrow cal(B)$,
    a _fibration morphism_ $F : cal(E) arrow cal(F)$ is a functor
    - that preserves cartesian morphisms
    - #box(width: 100%)[such that the following diagram commutes]
      #align(center, diagram(spacing: 2cm, $
          cal(E) edge("rr", F, ->) edge("dr", p, ->) && cal(F) edge("dl", q, ->) \
              & cal(B)
      $))

    Let $Fib_cal(B)$ be the category of fibration and fibration morphisms over $cal(B)$.
]

== Wow
#slide[
    Things happen
    #sym.circle.small #sym.circle.filled
]

#slide[
    At an amazing rate
]

= B
#slide[
    hello
]
// Local Variables:
// tp--master-file: "/home/adri/dev/notes/presentation.typ"
// End:
