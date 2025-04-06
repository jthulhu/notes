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
#let Sub = [*Sub*]
#let Pfct = [*Pfct*]
#let cod = [*cod*]
#let Cat = [*Cat*]

#set text(font: "New Computer Modern")
#show: university-theme.with(
    aspect-ratio: "4-3",
    config-common(
        // new-section-slide-fn: none,
    ),
    primary: colors.primary,
    config-info(
        title: [Grothendieck fibrations],
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

== Refinement system

#context counter(page).update(n => n - 1)

#slide[
    #show: bd => align(horizon, bd)
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
        A morphism $alpha : S arrow R$ in $cal(E)$ is _cartesian_ #pause when, for any morphism
        $beta : S' arrow R$ in $cal(E)$ and $g : p(S') arrow p(S)$ such that $
            p(beta) = p(alpha) compose g
        $ #pause
        there exists a unique lifting $gamma : S' arrow S$ of $g$ (ie $p(gamma) = g$) such
        that $
            beta = alpha compose gamma
        $
        #meanwhile
        #align(center, diagram(spacing: (3cm, 1cm), crossing-fill: colors.bg-gray, $
            \
                & S edge(alpha, ->) edge("dd", "-[]") & R edge("dd", "-[]") \
            \
                & p(S) edge(p(alpha), ->, label-side: #right) & p(R)
        $,
            pause,
            node((0, 0), $S'$, name: <beta-dom>),
            edge("drr", $beta$, "->", bend: 20deg),
            edge("dd", "-[]"),
            node((0, 2), $p(S')$),
            edge("dr", $g$, "->", label-side: right),
            edge("drr", $p(beta)$, "->", bend: 20deg, label-pos: 70%),
            edge((1, 1), "dd", "-[]", crossing: true),
            pause,
            edge(<beta-dom>, "dr", $gamma$, "->", "dashed")
        ))
    ]
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

== Example: the codomain fibration

#slide[
    #show: bd => align(horizon, bd)
    Consider the category $cal(B)^arrow$ whose objects are morphisms $f : X arrow Y$ in
    $cal(B)$.  For $f : X arrow Y$ and $g : A arrow B$ two objects of $cal(B)^arrow$,
    a morphism $(phi_1, phi_2) : f arrow g$ is a pair of morphisms $
        phi_1 &: X arrow A \
        phi_2 &: Y arrow B
    $
    such that the following diagram commutes
    #align(center, diagram(spacing: 3cm, $
        X edge(phi_1, ->) edge("d", f, ->) & A edge("d", g, ->) \
        Y edge(phi_2, ->) & B
    $))
    with obvious identities and compositions.
    #definition[
        The codomain functor $cod : cal(B)^arrow arrow cal(B)$ maps an object
        $f : X arrow Y$ to $Y$, and a morphism $(phi_1, phi_2)$ to $phi_2$.
    ]
]

#slide[
    #show: bd => align(horizon, bd)
    #theorem[
        If $cal(B)$ has pullbacks, then $cod$ is a fibration.
    ]
    
    Indeed, consider $X, Y : cal(B)$ and $f : X arrow Y$, as well as $g : Z arrow Y$
    ($g subset.sq Y$).  We have
    #align(center, diagram(spacing: (3cm, 1.5cm), $
        \
            & & Z edge("dd", g, ->) \
        \
            & X edge(f, ->) & Y
    $,
        pause,
        node((1, 1), $X times_Y Z$),
        edge("dd", "->"),
        edge("r", "->"),
        pause,
        node((0, 0), $A$),
        edge("drr", "->", bend: 20deg),
        edge("dd", "->"),
        node((0, 2), $B$),
        edge("dr", "->"),
        edge("drr", "->", bend: 20deg),
        edge((1, 1), "dd", "->", crossing: true),
        pause,
        edge((0, 0), "dr", "->", "dashed"),
    ))
]

= Fibered category
== Pseudofunctor

#slide[
    #show: bd => align(horizon, bd)
    #definition[
        We note $Pfct_cal(B)$ the category of contravariant pseudofunctor from $cal(B)$
        to $Cat$.
    ]
    An object $cal(P) : Pfct_cal(B)$ is the data of:
    - #box(width: 100%)[for $X : cal(B)$, a category $cal(P)_X : Cat$;]
    - for $f : X arrow Y$ a morphism in $cal(B)$, a functor
      $cal(P)_f : cal(P)_Y arrow cal(P)_X$;
    - for $X : cal(B)$, a natural isomorphism $i_X : cal(P)_id_X arrow.double id_cal(P)_X$,
      called the _pseudo identity_ of $cal(P)$ at $X$;
    - for $f,g$ two morphism in $cal(B)$, a natural isomorphism
      $c_(f,g) : cal(P)_(g compose f) arrow.double.long cal(P)_f compose cal(P)_g$, called
      the _pseudo composition_ of $cal(P)$ at $(f,g)$.

    Satisfying additionally two coherence conditions.
]


#slide[
    === Identity/composition coherence
    #show: bd => align(horizon, bd)
    For $X, Y : cal(B)$ and $f : X arrow Y$, we have
    #align(center, diagram(spacing: 5cm, $
        cal(P)_f edge(c_(f, id_Y), ->) edge("d", c_(id_X, f), ->) edge("dr", id_cal(P)_f, ->)
            & cal(P)_f compose cal(P)_id_Y
            edge("d", cal(P)_f compose i_Y, ->, label-side: #left) \
            cal(P)_id_X compose cal(P)_f edge(i_X compose cal(P)_f, ->, label-side: #right)
            & cal(P)_f
    $))
]
#slide[
    === Composition/composition coherence
    #show: bd => align(horizon, bd)
    For $W,X,Y,Z : cal(B)$, and $
        f &: W arrow.long X \
        g &: X arrow.long Y \
        h &: Y arrow.long Z
    $
    the following diagram commutes
    #align(center, diagram(spacing: 5cm, $
        cal(P)_(h compose g compose f) edge(c_(f, h compose g), ->) edge("d", c_(g compose f, h), ->)
            & cal(P)_f compose cal(P)_(h compose g) edge("d", cal(P)_f compose c_(g, h), ->) \
            cal(P)_(g compose f) compose cal(P)_h edge(c_(f, g) compose cal(P)_h, ->)
            & cal(P)_f compose cal(P)_g compose cal(P)_h
    $))
]

== Pseudofunctor morphism
#slide[
    #show: bd => align(horizon, bd)
    #definition[
        Let $cal(F)$, $cal(G) : Pfct_cal(B)$ be two pseudofunctors.  A morphism
        $nu : cal(F) arrow cal(G)$ is a pseudonatural transformation between
        $cal(F)$ and $cal(G)$.
    ]
    That is, a morphism $nu$ is the data:
    - #box(width: 100%)[for $X : cal(B)$, a morphism $nu_X : cal(F)_X arrow cal(G)_X$;]
    - for each morphism $f : X arrow Y$, a natural transformation
      #align(center, diagram(spacing: 3cm, $
          cal(P)_Y edge(nu_Y, ->) edge("d", cal(P)_f, ->)
              & cal(G)_Y edge("d", cal(G)_f, ->) edge("dl", nu_f, =>) \
              cal(P)_X edge(nu_X, ->) & cal(G)_X
      $))
      called the _pseudo naturality_ of $nu$ at $f$.

    $nu$ satisfies additionally two coherence conditions.
]

#slide[
    #show: bd => align(horizon, bd)
    For $X : cal(B)$, the following pasting diagram is $nu_X$
    #align(center, diagram(spacing: 5cm, $
        cal(P)_X edge("d", cal(P)_(id_X), ->) edge(nu_X, ->)
        edge("d", id_(cal(P)_X), ->, bend: #(-90deg))
            & cal(P)'_X edge("d", cal(G)_(id_X), ->, label-side: #right) edge("dl", nu_(id_X), =>)
            edge("d", id_(cal(G)_X), ->, bend: #90deg) \
            cal(P)_X edge(nu_X, ->) & cal(G)_X
    $,
        edge((-.3, .5), (-.6, .5), $i_X$, "=>"),
        edge((1.6, .5), (1.04, .5), $i^(-1)_X$, "=>"),
    ))
    that is, $
        (nu_X compose i_X) compose nu_id_X compose (i'_X^(-1) compose nu_X) = id_nu_X
    $
]

#slide[
    #show: bd => align(horizon, bd)
    For $X,Y,Z : cal(B)$, $f : X arrow Y$ and $g : Y arrow Z$, the following
    pasting is $nu_(g compose f)$
    #align(center, diagram(spacing: 5cm, $
        cal(P)_Z edge(nu_Z, ->) edge("d", cal(P)_g, ->) edge("dd", cal(P)_(g compose f), ->, bend: #(-50deg))
            & cal(G)_Z edge("d", cal(G)_g, ->) edge("dl", nu_g, =>)
            edge("dd", cal(G)_(g compose f), ->, bend: #50deg)\
            cal(P)_Y edge(nu_Y, ->) edge("d", cal(P)_f, ->)
            & cal(G)_Y edge("d", cal(G)_f, ->) edge("dl", nu_f, =>) \
            cal(P)_X edge(nu_X, ->) & cal(G)_X
    $,
        edge((1.5, 1), (1, 1), $c'_(f, g)$, "=>"),
        edge((0, 1), (-.5, 1), $c^(-1)_(f, g)$, "=>")
    ))
    that is, $
        nu_(g compose f) = (nu_X compose c^(-1)_(f, g)) compose (nu_f compose cal(P)_g)
        compose (cal(G)_f compose nu_g) compose (c'_(f,g) compose nu_Z)
    $
]

== Example: the subobject pseudofunctor
#slide[
    #show: bd => align(horizon, bd)
    For this example, assume that $cal(B)$ has pullbacks.

    Let $X : cal(B)$ be an object.
    #definition[
        The subobjects of $X$ is the category $Sub_X$ whose objects are monos into $X$,
        up to isomorphism.  Given $m, m' : Sub_X$, a morphism $f : m arrow m'$ is a
        morphism in $cal(B)$ making the following diagram commute
        #align(center, diagram(spacing: (1cm, 2cm), $
            A edge("dr", m, >->, label-side: #right) edge("rr", f, ->)
                & & B edge("dl", n, >->, label-side: #left) \
                & X
        $))
    ]
    Morphisms in $Sub_X$ are all monos in $cal(B)$, and between two objects there is at
    most one morphism, making $Sub_X$ a poset category.  Hence, we write $m <= n$ if
    there is a morphism $m arrow n$.
]

#slide[
    #show: bd => align(horizon, bd)
    Let $X, Y : cal(B)$ and $f : X arrow Y$.  If $m : Sub_Y$, say $m : A arrow.tail Y$.

    One can consider $Sub_f (m)$ defined by taking the following pullback
    #align(center, diagram(spacing: 3cm, $
        X times_Y A edge("d", Sub_f (m), >->) edge(->) & A edge("d", m, >->) \
        X edge(f, ->) & Y
    $))
    #pause
    Suppose $n <= m$:
    #align(center, diagram(spacing: 3cm, $
        X times_Y B edge("dd", Sub_f (n), >->, bend: #(-40deg)) edge("r", ->)
            & B edge("dd", n, >->, bend: #40deg) edge("d", <=, ->) \
        X times_Y A edge("d", Sub_f (m), >->, label-side: #left) edge(->) & A edge("d", m, >->) \
        X edge(f, ->) & Y
    $,
        pause,
        edge((0, 0), "d", $<=$, "->", "dashed")
    ))
    by pullback, there exists a map $X times_Y B arrow X times_Y A$ making the left triangle
    commute.
]

#slide[
    #show: bd => align(horizon, bd)
    We have shown that $Sub_X$ and $Sub_Y$ are categories, and, for $f : X arrow Y$,
    $ Sub_f : Sub_Y arrow Sub_X $ is a functor.  In fact, this operation is itself functorial
    in $f$, proving the
    #v(5%)
    #theorem[
        Subobjects $ Sub : cal(B)^op arrow Cat $
        form a presheaf into categories.
    ]
    #v(5%)
    The proof goes by pasting pullback diagrams together to form pullback diagrams.
]

= Equivalence

== Main theorem
#slide[
    #show: bd => align(horizon, bd)
    For a category $cal(B)$, we have the following equivalence
    #theorem[
        $ Fib_cal(B) tilde.equiv Pfct_cal(B) $
    ]
    This equivalence states that a fibration is exactly the collection of its fibers.

    One direction of this equivalence is known as the Grothendieck construction, which
    takes a collection of fibers above a category $cal(B)$ and constructs a fibration
    from its total category, on $cal(B)$, whose fibers are exactly those we started with.
]

// Local Variables:
// tp--master-file: "/home/adri/dev/notes/presentation.typ"
// End:
