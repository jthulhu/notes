#import "common.typ": *

#show: all.with([Notes on Representation of 2-groups], none)
#let Rep = [*Rep*]
#let Vect = [*Vect*]

= Preliminary notions

== 2-categories
#definition(title: [Strict 2-category])[
    A (strict) 2-category is a $Cat$-enriched category, that is, a category $cal(C)$ such that, for each
    two objects $X, Y in cal(C)$, $cal(C)(X, Y)$ is a category, such that the composition 
    $compose : cal(C)(X, Y) times cal(C)(Y, Z) -> cal(C)(X, Z)$ is a functor.
]

#definition(title: [Strict 2-functor])[
    A (strict) 2-functor between two 2-categories $cal(C)$ and $cal(D)$ is a functor from $cal(C)$ to
    $cal(D)$ seen as 1-categories, with an additional structure: for each two objects $X, Y in cal(C)$,
    $F_(X, Y) : cal(C)(X, Y) -> cal(D)(F(X), F(Y))$ is a functor and such that the
    following diagram commutes
    #align(center, diagram(spacing: 2cm, $
        cal(C)(X, Y) times cal(C)(Y, Z) edge("r", F_(X, Y) times F_(Y, Z), ->)  edge("d", *, ->)
            & cal(D)(F(X), F(Y)) times cal(D)(F(Y), F(Z)) edge("d", *, ->) \
            cal(C)(X, Z) edge("r", F_(X, Z), ->) & cal(D)(F(X), F(Z))
    $))
]

== Categories of internal categories
#definition(title: [Internal category])[
    Let $cal(C)$ be a category.  An _internal category_ in $cal(C)$ is the datum of two objects $C_0$
    and $C_1$ in $cal(C)$, as well as two morphisms $s, t : C_1 -> C_0$, named _source_ and _target_.
    
    Furthermore, there is an application $1 : C_0 -> C_1$ making the following diagram commute
    #align(center, diagram(spacing: 2cm, $
        & C_1 edge("dl", s, ->) edge("dr", t, ->) \
        C_0 & C_0 edge("l", id_C_0, ->) edge("u", 1, ->) edge("r", id_C_0, ->) & C_0
    $))
    as well as an application $diamond.small : C_1 times_C_0 C_1 -> C_1$ making the following diagram
    commute
    #align(center, diagram(spacing: 2cm, $
        && C_1 edge("dddll", s, ->, bend: #(-20deg)) edge("dddrr", t, ->, bend: #20deg) \
            && C_1 times_C_0 C_1 edge("u", diamond.small, ->) edge("dl", ->) edge("dr", ->) \
            & C_1 edge("dl", s, ->) edge("dr", t, ->) && C_1 edge("dl", s, ->) edge("dr", t, ->) \
            C_0 && C_0 && C_0
    $,
        edge(
            (2, 1.5),
            (2, 1),
            stroke: white,
            marks: (
                (inherit: "straight", sharpness: 45deg, size: 18, pos: .5, stroke: black),
            ),
        ),
    ))
    such that the two following diagrams commute
    #grid(
        columns: (1fr, 1fr),
        align: center + horizon, 
        diagram(spacing: 2cm, $
            C_1 edge("r", chevron s\, id_C_1 chevron.r, ->) edge("ddr", id_C_1, ->, label-side: #right)
                & C_0 times C_1 edge("d", 1 times C_1, ->, label-side: #left) \
                & C_1 times_C_0 C_1 edge("d", diamond.small, ->) \
                & C_1
        $),
        diagram(spacing: 2cm, $
            C_1 edge("r", chevron id_C_1\, t chevron.r, ->) edge("ddr", id_C_1, ->, label-side: #right)
                & C_1 times C_0 edge("d", C_1 times 1, ->, label-side: #left) \
                & C_1 times_C_0 C_1 edge("d", diamond.small, ->) \
                & C_1
        $)
    )
    as well as the following one
    #align(center, diagram(spacing: 2cm, $
        C_1 times_C_0 C_1 times_C_0 C_1 edge("r", C_1 times_C_0 diamond.small, ->) edge("d", diamond.small times_C_0 C_1, ->) 
            & C_1 times_C_0 C_1 edge("d", diamond.small, ->) \
            C_1 times_C_0 C_1 edge("r", diamond.small, ->) & C_1
    $))
]

#definition(title: [Internal functor])[
    Given two internal categories $C$ and $D$ in $cal(C)$, an _internal functor $F$ from $C$ to $D$_ is
    the datum of a morphism $
        F_0 : C_0 -> D_0
    $
    as well as a morphism $
        F_1 : C_1 -> D_1
    $
    making the following diagrams commute
    #grid(
        align: center + horizon, 
        columns: (1fr, 1fr, 1fr),
        diagram(spacing: 2cm, $
            C_1 edge("r", F_1, ->) edge("d", s, ->) & D_1 edge("d", s, ->) \
            C_0 edge("r", F_0, ->) & D_0
        $),
        diagram(spacing: 2cm, $
            C_0 edge("r", F_0, ->) edge("d", 1, ->) & D_0 edge("d", 1, ->) \
            C_1 edge("r", F_1, ->) & D_1
        $),
        diagram(spacing: 2cm, $
            C_1 edge("r", F_1, ->) edge("d", t, ->) & D_1 edge("d", t, ->) \
            C_0 edge("r", F_0, ->) & D_0
        $)
    )
    
    #align(center, diagram(spacing: 2cm, $
        C_1 times_C_0 C_1 edge("d", diamond.small, ->) edge("r", F_1 times F_1, ->)
            & D_1 times_D_0 D_1 edge("d", diamond.small, ->) \
            C_1 edge("r", F_1, ->) & D_1
    $))
]

#fact[
    For two internal functors $F : C -> D$ and $G : D -> E$, there exists a functor $
        G compose F : C -> E
    $
    such that $compose$ is associative.

    For any internal category $C$ of $cal(C)$, there exists an internal functor $id_C : C -> C$,
    that is an identity with respect to $compose$.
]

#definition(title: [Internal natural transformation])[
    Given two internal categories $C$ and $D$ of $cal(C)$, and two internal functors $F, G : C -> D$, 
    we call and _internal transformation from $F$ to $G$_ a morphism $alpha : C_0 -> D_1$ such that
    the following diagrams commute
    #grid(
        columns: (1fr, 1fr),
        align: center + horizon,
        diagram(spacing: 2cm, $
            C_0 edge("r", alpha, ->) edge("dr", F, ->, label-side: #right)
                & D_1 edge("d", s, ->, label-side: #left) \
                & D_0
        $),
        diagram(spacing: 2cm, $
            C_0 edge("r", alpha, ->) edge("dr", G, ->, label-side: #right)
                & D_1 edge("d", t, ->, label-side: #left) \
                & D_0
        $),
    )
    as well as the naturality diagram
    #align(center, diagram(spacing: 2cm, $
        C_1 edge("r", chevron C_1\, t chevron.r, ->) edge("d", chevron s\, C_1 chevron.r, ->)
            & C_1 times_C_0 C_0 edge("d", F times alpha, ->) \
            C_0 times_C_0 C_1 edge("d", alpha times G_1, ->) 
            & D_1 times_D_0 D_1 edge("d", diamond.small, ->) \
            D_1 times_D_0 D_1 edge("r", diamond.small, ->) 
            & D_1
        
    $))
]

#fact[
    The class of internal categories of $cal(C)$, with internal functors as morphisms and internal
    natural transformations as 2-cells, forms a 2-category, noted $Cat_cal(C)$.
]

= Representation of 2-groups
Let $KK$ be a fixed field for the rest of the section.

== Representation of a group
Let $G$ be a group.

#definition(title: [Representation of $G$])[
    A _representation of $G$_ is a $KK$-linear space $V$, with a linear action $G arrow.cw V$.
    
    Given two representations $V$ and $W$ of $G$, a morphism of representations $V -> W$ is a
    linear map $f : V -> W$ such that, for every $g in G$, and $v in V$, we have $
        f(g dot.c v) = g dot.c f(v)
    $
]
#exercise[
    Prove that representations of $G$ forms a category $Rep_G$
]
#exercise[
    Show that $
        Rep_G tilde.eq [G, Vect_KK]
    $
    where $[G, Vect_KK]$ is the category of functors from $G$ seen as a category, and $Vect_KK$
    is the category of linear spaces with linear maps as morphisms.
]

== 2-group
#definition(title: [$2$-group], breakable: false)[
    A $2$-group is a $2$-category, with exactly one object, where every 1-cell and 2-cell are isomorphisms.
]

#definition(title: [2-representation])[
    Let $cal(G)$ be a 2-group.  A _2-representation of $cal(G)$_ is a 2-functor $
        cal(G) --> Cat_(Vect_KK)
    $
]

#theorem[
    A 2-group $cal(G)$ is exactly the data of a group $G$, a group $H$ with a morphism $t : H -> G$, as well
    as an action $G arrow.cw H$ such that, for all $g in G$ and $h in G$, $
        t(g dot.c h) = g t(h) g^(-1)
    $
    and for $h, h' in H$, we have $
        (t(h) dot.c h') h = h h'
    $
    with $cal(G)_1 = G$ and $cal(G)_2 = H times.r G$.
]
#proof[
    #show math.equation: set block(breakable: true)
    Suppose we have a group $H$ with a morphism $t : H -> G$, and an action $G arrow.cw H$.  Let us 
    consider the 2-group $cal(G)$ upon $G$, with 2-cells defined by $cal(G)(g, g') = { h in H
    | t(h) g = g' }$. The identity at $g in G$ is given by $(1_H, g)$.  Let $(h, g) : g => g'$ and $(h', g')
    : g' => g''$.  The vertical composition is given by $
        h' compose h = h' h : g => g''
    $
    Indeed, $
        t(h' h) g &= t(h') t(h) g \
            &= t(h') g' \
            &= g''
    $
    Let $h : g_1 => g_2$ and $h' : g'_1 => g'_2$.  Their horizontal composition is given by $
        h * h' = h (g_1 dot.c h')
    $
    Indeed, $
        t(h (g_1 dot.c h')) g_1 g'_1 &= t(h) t(g_1 dot.c h') g_1 g'_1 \
            &= t(h) g_1 t(h') g_1^(-1) g_1 g'_1 \
            &= (t(h) g_1) (t(h') g'_1) \
            &= g_2 g'_2
    $
    Let us now check functoriality, that is, in the following situation
    #align(center, diagram(spacing: 2cm, $
        * edge("r", g_1, ->, bend: #60deg) edge("r", g_2, ->, label-pos: #70%) edge("r", g_3, ->, bend: #(-60deg))
            & * edge("r", g'_1, ->, bend: #60deg) edge("r", g'_2, ->, label-pos: #70%) edge("r", g'_3, ->, bend: #(-60deg))
            & *
    $,
        edge((.5, -.3), (.5, -.05), $h_1$, "=>"),
        edge((.5, .05), (.5, .3), $h_2$, "=>"),
        edge((1.5, -.3), (1.5, -.05), $h'_1$, "=>"),
        edge((1.5, .05), (1.5, .3), $h'_2$, "=>"),
    ))
    We have $
        (h_2 * h'_2) compose (h_1 * h'_1) &= (h_2 * h'_2) (h_1 * h'_1) \
            &= h_2 (g_2 dot.c h'_2) h_1 (g_1 dot.c h'_1) \
            &= h_2 (t(h_1) g_1 dot.c h'_2) h_1 (g_1 dot.c h'_1) \
            &= h_2 (t(h_1) dot.c g_1 dot.c h'_2) h_1 (g_1 dot.c h'_1) \
            &= h_2 h_1 (g_1 dot.c h'_2) (g_1 dot.c h'_1) \
            &= h_2 h_1 (g_1 dot.c (h'_2 h'_1)) \
            &= (h_2 h_1) * (h'_2 h'_1) \
            &= (h_2 compose h_1) * (h'_2 compose h'_1)
    $
    
    Conversely, suppose we have a 2-group $cal(G)$.  Let us define $G$ be the group of 1-cells of $cal(G)$.
    Let $H$ be the group of 2-cells of the form $cal(G)(1, g)$ for some $g$.  Let us show that this is
    a group, for the multiplication given by, for $alpha : 1 => g$ and $beta : 1 => g'$, $
        alpha dot.c beta := (alpha compose (beta * g'^(-1))) * g' : 1 => g g'
    $
    #align(center, diagram(spacing: 2cm, $
        * edge("r", g', ->, label-side: #right) edge("r", 1, ->, bend: #60deg) edge("rr", g, ->, bend: #(-60deg))
            & * edge("r", g'^(-1), ->)
            & * edge("r", g', ->, label-side: #right)
            & *
    $,
        edge((.5, -.3), (.5, -.05), $beta$, "=>"),
        edge((1, .05), (1, .7), $alpha$, "=>"),
    ))
    It has a neutral $id_1 : 1 => 1$, indeed, for $alpha : 1 => g$, we have
    $
        #box(baseline: 60%, diagram(spacing: 2cm, $
            * edge("r", 1, ->, bend: #60deg) edge("r", 1, ->, label-side: #right) edge("rr", g, ->, bend: #(-60deg), label-side: #right)
                & * edge("r", 1, ->)
                & * edge("r", 1, ->)
                & *
        $,
            edge((.5, -.3), (.5, -.05), $id_1$, "=>"),
            edge((1, .05), (1, .7), $alpha$, "=>"),
        ));
        quad = quad
        #box(baseline: 70%, diagram(spacing: 2cm, $
            * edge("r", 1, ->) edge("r", g, ->, bend: #(-60deg)) & *
        $,
            edge((.5, .1), (.5, .35), $alpha$, "=>"),
        ))
    $
    and similarly,
    $
        #box(baseline: 57%, diagram(spacing: 2cm, $
            * edge("rr", 1, ->, bend: #(-60deg)) edge("r", 1, ->, bend: #60deg) edge("r", g', ->, label-side: #right)
                & * edge("r", g'^(-1), ->)
                & * edge("r", g', ->) 
                & *
        $,
            edge((.5, -.3), (.5, -.05), $beta$, "=>"),
            edge((1, .05), (1, .7), $id_1$, "=>"),
        ));
        quad = quad
        #box(baseline: 25%, diagram(spacing: 2cm, $
            * edge("r", 1, ->, bend: #60deg) edge("r", g', ->, label-side: #right) & *
        $,
            edge((.5, -.3), (.5, -.05), $beta$, "=>"),
        ));
    $
    
    and the inverse of $alpha : 1 => g$, is $alpha^(-1) * g^(-1)$.  
    Indeed, $
        #box(baseline: 60%, diagram(spacing: 2cm, $
            * edge("rr", g^(-1), ->, bend: #(-60deg)) edge("r", 1, ->, bend: #60deg) edge("r", g, ->, label-side: #right)
                & * edge("r", g^(-1), ->)
                & * edge("r", g, ->)
                & *
        $,
            edge((.5, -.3), (.5, -.05), $alpha$, "=>"),
            edge((1, .05), (1, .7), $alpha^(-1) * g^(-1)$, "=>"),
        ));
        quad = quad 
        #box(baseline: 45%, diagram(spacing: 2cm, $
            * edge("r", 1, ->, bend: #60deg) edge("r", 1, ->, bend: #(-60deg)) & *
        $,
            edge((.5, -.3), (.5, .3), $id_1$, "=>")
        ))
    $
    and
    $
        #box(baseline: 60%, diagram(spacing: 2cm, $
            * edge("rrr", g, ->, bend: #(-45deg)) edge("r", g, ->, bend: #60deg) edge("r", 1, ->, label-side: #right)
                & * edge("r", g^(-1), ->)
                & * edge("r", g, ->)
                & * edge("r", g^(-1), ->)
                & *
        $,
            edge((.5, -.3), (.5, -.05), $alpha^(-1)$, "=>"),
            edge((1.5, .05), (1.5, .7), $alpha$, "=>"),
        ))
        quad = quad 
        #box(baseline: 45%, diagram(spacing: 2cm, $
            * edge("r", 1, ->, bend: #60deg) edge("r", 1, ->, bend: #(-60deg)) & *
        $,
            edge((.5, -.3), (.5, .3), $id_1$, "=>")
        ))
    $
    
    Let's now exhibit an action of $G arrow.cw H$. For $g in G$ and $alpha : 1 => g'$, $
        g dot.c alpha quad &= quad #box(baseline: 50%, diagram(spacing: 2cm, $
            * edge("r", g, ->)
                & * edge("r", 1, ->, bend: #60deg) edge("r", g', ->, bend: #(-60deg))
                & * edge("r", g^(-1), ->) 
                & *
        $,
            edge((1.5, -.3), (1.5, .3), $alpha$, "=>"),
        )) \
            &= quad g * alpha * g^(-1)
    $
    
    We have $
        (g_1 g_2) dot.c alpha &= (g_1 g_2) * alpha * (g_1 g_2)^(-1) \
            &= g_1 * g_2 * alpha * g_2^(-1) * g_1^(-1) \
            &= g_1 dot.c (g_2 dot.c alpha)
    $
    hence it is an action.  Let's now show that it is a group morphism: let $g in G$, $alpha : 1 => g_1$
    and $beta : 1 => g_2$.  We have $
        g dot.c (alpha dot.c beta) &= g^(-1) * g_2 * (alpha compose (beta * g_2^(-1))) * g \
            &= quad #box(baseline: 51%, diagram(spacing: 2cm, $
                * edge("r", g^(-1), ->) 
                    & * edge("r", 1, ->, bend: #60deg) edge("r", g_2, ->, label-side: #right) edge("rr", g_1, ->, bend: #(-45deg))
                    & * edge("r", g_2^(-1), ->) 
                    & * edge("r", g, ->)
                    & *
            $,
                edge((1.5, -.3), (1.5, -.05), $beta$, "=>"),
                edge((2, .05), (2, .5), $alpha$, "=>"),
            )); \
            &= quad #box(baseline: 60%, diagram(spacing: 2cm, $
                * edge("r", g^(-1), ->) edge("rrrr", g^(-1) g_1 g, ->, bend: #(-40deg))
                    & * edge("r", 1, ->, bend: #60deg) edge("r", g_2, ->, label-side: #right)
                    & * edge("r", g, ->)
                    & * edge("r", (g^(-1) g_2 g)^(-1), ->)
                    & * edge("r", g^(-1) g_2 g^(-1), ->)
                    & *
            $,
                edge((1.5, -.3), (1.5, -.05), $beta$, "=>"),
                edge((2, .05), (2, .7), $g dot.c alpha$, "=>")
            )); \
            &= (g dot.c alpha) dot.c (g dot.c beta)
    $
    
    Finally, there is a morphism $
        t &:& H &--> G \
            && (alpha : 1 => g) &mapsto.long g
    $
    Let's check that, for $h, h' in H$, we have $
        (t(h) dot.c h') h = h h'
    $
    $
        (t(h) dot.c h') h quad &= quad #box(baseline: 70%, diagram(spacing: 2cm, $
            * edge("r", t(h), ->, label-side: #right) edge("r", 1, ->, bend: #60deg) edge("d", t(h), ->)
                & * edge("r", t(h)^(-1), ->)
                & * edge("r", t(h), ->)
                & * \
                * edge("rr", t(h'), ->)
                & & * edge("u", t(h)^(-1), ->)
        $,
            edge((1, .1), (1, .7), $t(h) dot.c h'$, "=>"),
            edge((.5, -.3), (.5, -.05), $h$, "=>"),
        )); \
            &= quad #box(baseline: 48%, diagram(spacing: 2cm, $
                * edge("r", t(h), ->, label-side: #right) edge("r", 1, ->, bend: #60deg)
                    & * edge("r", 1, ->) edge("r", t(h'), ->, bend: #(-60deg))
                    & * edge("r", t(h)^(-1), ->)
                    & * edge("r", t(h), ->)
                    & *
            $,
                edge((1.5, .05), (1.5, .35), $h'$, "=>"),
                edge((.5, -.3), (.5, -.05), $h$, "=>"),
            )); \
            &= quad #box(baseline: 48%, diagram(spacing: 2cm, $
                * edge("r", t(h), ->, label-side: #right) edge("r", 1, ->, bend: #60deg)
                    & * edge("r", 1, ->) edge("r", t(h'), ->, bend: #(-60deg))
                    & *
            $,
                edge((1.5, .05), (1.5, .35), $h'$, "=>"),
                edge((.5, -.3), (.5, -.05), $h$, "=>"),
            )); \
            &= quad #box(baseline: 48%, diagram(spacing: 2cm, $
                * edge("r", t(h), ->, label-side: #right, bend: #(-60deg)) edge("r", 1, ->)
                    & * edge("r", 1, ->, bend: #60deg) edge("r", t(h'), ->, label-side: #right)
                    & *
            $,
                edge((.5, .05), (.5, .35), $h$, "=>"),
                edge((1.5, -.3), (1.5, -.05), $h'$, "=>"),
            )); \
            &= quad #box(baseline: 48%, diagram(spacing: 2cm, $
                * edge("rrr", t(h), ->, label-side: #right, bend: #(-45deg)) edge("r", 1, ->)
                    & * edge("r", 1, ->, bend: #60deg) edge("r", t(h'), ->, label-side: #right)
                    & * edge("r", t(h')^(-1), ->)
                    & * edge("r", t(h'), ->)
                    & *
            $,
                edge((1.5, .3), (1.5, .7), $h$, "=>"),
                edge((1.5, -.3), (1.5, -.05), $h'$, "=>"),
            )); \
            &= quad #box(baseline: 48%, diagram(spacing: 2cm, $
                * edge("rr", t(h), ->, label-side: #right, bend: #(-45deg)) edge("r", 1, ->, bend: #60deg) edge("r", t(h'), ->, label-side: #right)
                    & * edge("r", t(h')^(-1), ->)
                    & * edge("r", t(h'), ->)
                    & *
            $,
                edge((1, .05), (1, .5), $h$, "=>"),
                edge((.5, -.3), (.5, -.05), $h'$, "=>"),
            )); \
            &= h h'
    $
]

== 2-representation of a 2-group
=== From the groupoid perspective
Let $cal(G)$ be a fixed 2-group, and $F : cal(G) -> Cat_(Vect_KK)$ be a 2-representation.  This is the data of
an internal category $V := V_1 arrows V_0$ in $Vect_KK$, such that, for every $g in cal(G)_1$, there is a functor $
    g dot.c - : V -> V
$
that is, linear maps $g dot.c_0 - : V_0 -> V_0$ and $g dot.c_1 - : V_1 -> V_1$ such that the following
equations hold $
    g dot.c_1 1_v &= 1_v & #[ for every $v in V_0$] \
    s(g dot.c_1 f) &= g dot.c_0 s(f) & #[ for every $f in V_1$] \
    t(g dot.c_1 f) &= g dot.c_0 t(f) & #[ for every $f in V_1$] \
    g dot.c_1 (f' diamond.small f) &= (g dot.c_1 f') diamond.small (g dot.c_1 f) & #[ for every $f, f' in V_1$ such that $t(f') = s(f)$]
$

The 1-functoriality of $F$ expresses exactly that $g arrow.cw V_0$ and $g arrow.cw V_1$, that is, the
following equations hold: $
    e dot.c_0 v &= v & #[ for $v in V_0$] \
    e dot.c_1 f &= f & #[ for $f in V_1$] \
    (g g') dot.c_0 v &= g dot.c_0 (g' dot.c_0 v) & #[ for $v in V_0$] \
    (g g') dot.c_1 f &= g dot.c_1 (g' dot.c_1 f) & #[ for $f in V_1$]
$ 

Let's now look at the 2-functoriality part of $F$.  For $g, g' in G$ elements of $G$, and $alpha : g => g'$ a
2-cell.  We have that $
    alpha dot.c - : g dot.c_1 - => g' dot.c_1 -
$
is an internal natural transformation, that is, a linear map $alpha dot.c - : V_0 -> V_1$ such that $
    s(alpha dot.c v) &= g dot.c_0 v & #[ for $v in V_0$] \
    t(alpha dot.c v) &= g' dot.c_0 v & #[ for $v in V_0$] \
    (alpha dot.c t(f)) diamond.small (g dot.c_1 f) &= (g' dot.c_1 f) diamond.small (alpha dot.c s(f))
        & #[ for every $f in V_1$]
$


The $2$-functoriality implies that, for every $alpha : g => g'$ and $beta : g' => g''$, for $v in V_0$,
we have $
    (beta compose alpha) dot.c v = (beta dot.c v) diamond.small (alpha dot.c v)
$
and, for $g in G$, $
    id_g dot.c v = 1_v
$

Furthermore, for $alpha : g_1 => g_2$ and $beta : g'_1 => g'_2$, we have $
    (beta * alpha) dot.c v &= (g'_2 dot.c_1 alpha dot.c v) diamond.small (beta dot.c g_1 dot.c_0 v) \
        &= (beta dot.c g_2 dot.c_0 v) diamond.small (g'_1 dot.c_1 alpha dot.c v)
$
The last equality stems from naturality of $beta dot.c -$.

=== From the crossed module perspective
Let us now consider the case of a 2-group presented as a group action $G arrow.cw H$ with a morphism
$t : H -> G$ satisfying $
    t(h) dot.c h' &= h h' h^(-1) \
    t(g dot.c h) &= g t(h) g^(-1)
$
A 2-representation is the data of an internal category $V := V_1 arrows V_0$ in $Vect_KK$ such that,
for every $g in G$, there is a functor $g dot.c - : V -> V$, that is, linear maps $g dot.c_0 - : V_0 -> 
V_0$ and $g dot.c_1 - : V_1 -> V_1$ making the following equations hold: $
    g dot.c_1 1_v &= 1_v & #[ for every $v in V_0$] \
    s(g dot.c_1 f) &= g dot.c_0 s(f) & #[ for every $f in V_1$] \
    t(g dot.c_1 f) &= g dot.c_0 t(f) & #[ for every $f in V_1$] \
    g dot.c_1 (f' diamond.small f) &= (g dot.c_1 f') diamond.small (g dot.c_1 f) & #[ for every $f, f' in V_1$ such that $t(f) = s(f')$]
$

The 1-functoriality of $F$ expresses exactly that $G arrow.cw V_0$ and $G arrow.cw V_1$, that is, the 
following equations hold: $
    e dot.c_0 v &= v & #[ for $v in V_0$] \
    e dot.c_1 f &= f & #[ for $f in V_1$] \
    (g g') dot.c_0 v &= g dot.c_0 (g' dot.c_0 v) & #[ for $v in V_0$] \
    (g g') dot.c_1 f &= g dot.c_1 (g' dot.c_1 f) & #[ for $f in V_1$]
$

Let's now look at the $2$-functoriality of $F$.  For every $g in G$ and $h in H$,
we have a linear map $h dot.c_g - : V_0 -> V_1$ satisfying the following equations $
    s(h dot.c_g v) &= g dot.c_0 v \
    t(h dot.c_g v) &= t(h)g dot.c_0 v \
    (h dot.c_g t(f)) diamond.small (g dot.c_1 f) &= (t(h)g dot.c_1 f) diamond.small (h dot.c_g s(f))
        &" (naturality)"
$
Furthermore, for $h, h' in H$ and $g in G$, and $v in V_0$, we have $
    1_H dot.c_g v &= 1_v \
    (h'h) dot.c_g v &= h' dot.c_(t(h)g) h dot.c_g v
$
Finally, for $h, h' in H$ and $g, g' in G$, and $v in V_0$, we have $
    h(g dot.c h') dot.c_(g g') v
        &= (t(h)g dot.c_1 (h' dot.c_g' v)) diamond.small (h dot.c_g (g' dot.c_0 v)) &quad& (1)\
        &= (h dot.c_g (t(h')g' dot.c_0 v)) diamond.small (g dot.c_1 (h' dot.c_g' v)) && (2)
$

(the last equality holds by naturality of $h' dot.c_g' -$).  Consider the group morphism $
    t &:& H times.r G &--> G \
        && (h, g) &mapsto.long t(h)g
$
which is, indeed, a morphism: $
    t((h, g)(h', g')) &= t(h (g dot.c h'), g g') \
        &= t(h (g dot.c h'))g g' \
        &= t(h) t(g dot.c h') g g' \
        &= t(h) g t(h') g' \
        &= t(h, g) t((h', g'))
$

The equation (1) is exactly the commutativity of the following diagram
#align(center, diagram(spacing: 2cm, $
    text(#red, (H times.r G)) times text(#blue, (H times.r G)) times text(#green, V_0) edge("r", text(#red, -) dot.c text(#blue, -) times text(#green, V_0), ->) edge("d", chevron t\, text(#red, H times.r G) chevron.r times chevron text(#blue, H times.r G)\, pi_2 chevron.r times Delta_text(#green, V_0), ->)
        & (H times.r G) times text(#green, V_0) edge("dddd", - dot.c text(#green, -), ->) \
        text(#red, G) times text(#red, (H times.r G)) times text(#blue, (H times.r G)) times text(#blue, G) times text(#green, V_0) times text(#green, V_0) edge("d", ~, ->, label-angle: #auto, label-sep: #(-3pt)) \
        text(#red, G) times text(#blue, (H times.r G)) times text(#green, V_0) times text(#red, (H times.r G))
        times text(#blue, G) times text(#green, V_0) 
        edge("d", text(#red, G) times text(#blue, -) dot.c text(#green, -) times text(#red, (H times.r G)) times text(#blue, -) dot._0 text(#green, -), ->) \
        text(#red, G) times V_1 times text(#red, (H times.r G)) times V_0
        edge("d", text(#red, -) dot.c_1 - times text(#red, -) dot.c -, ->) \
        V_1 times_V_0 V_1 edge("r", diamond.small, ->) & V_1
$))

and the equation (2) is exactly the commutativity of the following diagram
#align(center, diagram(spacing: 2cm, $
    text(#red, (H times.r G)) times text(#blue, (H times.r G)) times text(#green, V_0)
    edge("r", text(#red, -) dot.c text(#blue, -) times text(#green, V_0), ->)
    edge("d", chevron pi_2\, text(#red, (H times.r G)) chevron.r times chevron t\, text(#blue, (H times.r G)) chevron.r times Delta_text(#green, V_0), ->)
        & (H times.r G) times text(#green, V_0) edge("dddd", - dot.c text(#green, -), ->) \
        text(#red, G) times text(#red, (H times.r G)) times text(#blue, G) times text(#blue, (H times.r G))
        times text(#green, V_0) times text(#green, V_0)
        edge("d", ~, label-angle: #auto, label-sep: #(-2pt), ->) \
        text(#red, (H times.r G)) times text(#blue, G) times text(#green, V_0) times text(#red, G)
        times text(#blue, (H times.r G)) times text(#green, V_0)
        edge("d", text(#red, (H times.r G)) times text(#blue, -) dot.c_0 text(#green, -) times text(#red, G) times text(#blue, -) dot.c text(#green, -), ->) \
        text(#red, (H times.r G)) times V_0 times text(#red, G) times V_1
        edge("d", text(#red, -) dot.c - times text(#red, -) dot.c_1 -, ->) \
        V_1 times_V_0 V_1 edge("r", diamond.small, ->) & V_1
    
$))

// Local Variables:
// typst-preview--master-file: "./representation-of-2-groups.typ"
// End:
