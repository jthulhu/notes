#import "common.typ": *

#show: all.with([Notes of representation of 2-groups], none)
#let Rep = [*Rep*]
#let Vect = [*Vect*]

= Preliminary notions

== 2-category
#definition(title: [Strict 2-category])[
    A (strict) 2-category is a $Cat$-enriched category, that is, a category $cal(C)$ such that, for each
    two objects $X, Y : cal(C)$, $cal(C)(X, Y)$ is a category, such that the composition 
    $compose : cal(C)(X, Y) times cal(C)(Y, Z) -> cal(C)(X, Z)$ is a functor.
]

#definition(title: [Strict 2-functor])[
    A (strict) 2-functor between two 2-categories $cal(C)$ and $cal(D)$ is a functor from $cal(C)$ to
    $cal(D)$ seen as 1-categories, with an additional structure: for each two objects $X, Y : cal(C)$,
    $F_(X, Y) : cal(C)(X, Y) -> cal(D)(F(X), F(Y))$ is a functor.
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
    we call and _internal transformation from $F$ to $G$_ a morphism $nu : C_0 -> D_1$ such that
    the following diagrams commute
    #grid(
        columns: (1fr, 1fr),
        align: center + horizon,
        diagram(spacing: 2cm, $
            C_0 edge("r", nu, ->) edge("dr", F, ->, label-side: #right)
                & D_1 edge("d", s, ->, label-side: #left) \
                & D_0
        $),
        diagram(spacing: 2cm, $
            C_0 edge("r", nu, ->) edge("dr", G, ->, label-side: #right)
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
    linear map $f : V -> W$ such that, for every $g : G$, and $v : V$, we have $
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
#definition(title: [$2$-group])[
    A $2$-group is a $2$-category, with exactly one object, and where every 1-cell is an isomorphism.
]
#definition(title: [2-representation])[
    Let $G$ be a 2-group.  A _2-representation of $G$_ is a 2-functor $
        G --> Cat_(Vect_KK)
    $
]

== 2-representation of a 2-group
Let $G$ be a fixed 2-group, and $F : G -> Cat_(Vect_KK)$ be a 2-representation.  This is the data of
an internal category $V := V_1 arrows V_0$ in $Vect_KK$, such that, for every $g : G$, there is a functor $
    g dot.c - : V -> V
$
that is, linear maps $g dot.c - : V_0 -> V_0$ and $g dot.c - : V_1 -> V_1$.  The 1-functoriality of $F$
expresses exactly that $g arrow.cw V_0$ and $g arrow.cw V_1$, that is, the following equations hold: $
    e dot.c v &= v & #[ for $v : V_0$] \
    e dot.c f &= f & #[ for $f : V_1$] \
    (g g') dot.c v &= g dot.c (g' dot.c v) & #[ for $v : V_0$] \
    (g g') dot.c f &= g dot.c (g' dot.c f) & #[ for $f : V_1$]
$ 
Furthermore, the following equations hold $
    g dot.c 1_v &= 1_v & #[ for every $v : V_0$] \
    s(g dot.c f) &= g dot.c s(f) & #[ for every $f : V_1$] \
    t(g dot.c f) &= g dot.c t(f) & #[ for every $f : V_1$] \
    g dot.c (f' diamond.small f) &= (g dot.c f') diamond.small (g dot.c f) & #[ for every $f, f' : V_1$ such that $t(f') = s(f)$]
$

Let's now look at the 2-functoriality part of $F$.  For $g, g' : G$ elements of $G$, and $alpha : g => g'$ a
2-cell.  We have that $
    alpha dot.c - : g dot.c - => g' dot.c -
$
is a natural transformation, that is, for every $v : V_0$, there is a $
    alpha dot.c v : V_1
$
such that $
    s(alpha dot.c v) &= g dot.c v & #[ for $v : V_0$] \
    t(alpha dot.c v) &= g' dot.c v & #[ for $v : V_0$] \
    (alpha dot.c t(f)) diamond.small (g dot.c f) &= (g' dot.c f) diamond.small (alpha dot.c s(f))
        & #[ for every $f : V_1$]

$


The $2$-functoriality implies that, for every $alpha : g => g'$ and $beta : g' => g''$, for $v : V_0$,
we have $
    (beta compose alpha) dot.c v = (beta dot.c v) diamond.small (alpha dot.c v)
$
and, for $g : G$, $
    id_g dot.c v = 1_v
$

// Local Variables:
// typst-preview--master-file: "./representation-of-2-groups.typ"
// End:
