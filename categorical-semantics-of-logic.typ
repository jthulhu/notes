#import "common.typ": *

#let CCat = [*CCat*]
#let Zero = [*0*]
#let One = [*1*]
#let Two = [*2*]
#let dom = [dom]
#let cod = [cod]
#let Mod = [*Mod*]
#let Shp = [*Shp*]
#let Vect = [*Vect*]
#let colim = math.op([colim], limits: true)

#show: all.with([Notes on categorical semantics of logic], none)
#set heading(supplement: [Chapter])

#let entail = $op(tack, limits: #false)$

#heading(numbering: none, outlined: false)[Introduction]

The idea that motivates the current note is that every class of theories can be expressed as a category
of sufficiently structure rich categories.  For instance, when a category has a terminal object $1$, one
can see objects of this category as collection of their elements, where an _element of an object $A$_ is
simply a morphism $1 -> A$.  This suggests that, to be able to speak categorically of theories that exhibit
constants, one just needs the "ambient category" to have a terminal object.

Taking this idea further, one can see classes of categories having sufficiently rich structure as those
categories that can be taken as "ambient" categories in which to develop a given theory.  We will begin
by investigating categories in which one can take limits of a given shape.  Each class of shapes will
produce a class of theories one can speak of, but, most importantly, the categorical structure of the
class of shapes, $Shp$, will give us a way to _mix_ theories of different kind.

For instance, one can see categories as "higher sets", that is, a (large) set equiped with morphisms.
This suggests that in order to get a "higher" version of a theory that usually takes place in sets,
one can perform the theory with categories rather than sets.  For instance, given a field $KK$, one
can consider vector spaces over $KK$, but also vector spaces over $KK$ internal to $Cat$.  However,
we can also recover the same models by considering models of a _product theory_ (the product of then
theory of vector spaces, and the theory of categories).  One therefore derives $2"-"Vect_KK := Vect_KK 
times Cat$, the theory of 2-vector spaces.  The main interest here of doing so is that one recovers the
ability to interpret this theory in different categories.

#show heading.where(level: 1): it => { 
    pagebreak(weak: true);
    it.supplement
    [ ]
    if it.numbering != none {
        context counter(heading).display(it.numbering)
        [ ]
    }
    it.body
    parbreak()
}

= Shape calculus
For this section, consider $cal(F)$ a class of (small) categories.  Elements of $cal(F)$ are called
_shapes_.

#definition(title: [$cal(F)$-complete category])[
    A $cal(F)$-complete category is a category that has all limits of all shapes $cal(S) : cal(F)$.
]

// $
//     cal(C)(X, lim (lim_{*_2 quad *_3} F) times (lim_{*_2 quad *_3} F) xarrow(F(*_2 -> *_1) compose pi_1, sym: arrows)_(F(*_3 -> *_1) compose pi_2) F(*_1)) &tilde.equiv \
//     cal(C)(X, lim_{*_2 -> *_1 <- *_3} F) &tilde.equiv cal(C)^{*_2 -> *_1 <- *_3}(X, F) \
//         &tilde.equiv cal(C)(X, lim_{*_5 arrows *_4} cases(*_5 &mapsto.long \_, *_4 &mapsto.long lim_{*_2 quad *_3} F))
// $

== Category of shapes

At first, we will consider a fixed $cal(F)$, and develop the theory around it.  For instance, we will
see how to compute the product of two $cal(F)$ theories.  However, this doesn't inform us on how to
do the product of an $cal(F)$ theory with a $cal(F)'$ theory: for instance, the theory of higher
vector spaces will be built as a product of the theory of vector spaces with the theory of higher
categories.

#definition(title: [Category of shapes])[
    Let $Shp$ be the preorder category whose objects are collection of categories, and there is a morphism
    from $cal(F)$ to $cal(F)'$ if every $cal(F)'$-complete category $cal(C)$ is also $cal(F)$-complete.
]

== $cal(F)$-complete categories

Let us note $cal(F)Cat$ the category of $cal(F)$-complete categories with morphisms $cal(S)$-continuous
functors for every $cal(S) : cal(F)$.

#example[
    The category of cartesian categories $CCat$ is a category of $cal(F)$-complete categories for $
        cal(F) := {Zero, 2}
    $
    where $2$ is the walking pair of points.
]

#example[
    The category of (finitely) complete categories is a category of $cal(F)$-complete category, by
    taking $cal(F)$ to be the class of all (finite) categories.
]

#remark[
    Multiple different $cal(F)$ can lead to the same category $cal(F)Cat$.  For instance, equalizers
    and finite products are enough to have all finite limits; similarly, having pullbacks and a terminal
    object is enough to have all finite limits.
]

The cornerstone of the theory of $cal(F)$-complete categories is stated as follows.

#theorem[
    $cal(F)Cat$ is cartesian closed.
]
#proof[
    First of all, $cal(F)Cat$ has a terminal object: $One$.  Indeed, $One$ is complete.  Furthermore,
    every functor $cal(C) xarrow(!) One$ is complete.  Let us now consider $cal(C), cal(D) : cal(F)Cat$
    two categories, and let us show that $cal(C) times cal(D)$ is in $cal(F)Cat$.  Let $cal(S) : cal(F)$
    be a shape, and $F : cal(S) -> cal(C) times cal(D)$ a functor.  We can write $F = chevron F_1, F_2 
    chevron.r$.  Let us show that $(lim F_1, lim F_2)$ is a limit of $F$.  This stems from the following
    (natural) identities, for $(X, Y) : cal(C) times cal(D)$: $
        (cal(C) times cal(D))((X, Y), (lim F_1, lim F_2)) &= cal(C)(X, lim F_1) times cal(D)(Y, lim F_2) \
            &tilde.equiv (X => F_1) times (Y => F_2) \
            &tilde.equiv (X, Y) => F_1 times F_2
    $
    By the particular choice of limits in $cal(C) times cal(D)$ that we have exhibited, we can immediately
    deduce that $pi_cal(C) : cal(C) times cal(D) -> cal(C)$ and $pi_cal(D) : cal(C) times cal(D) -> cal(D)$
    are continuous for shapes in $cal(F)$.  It is immediate that $cal(C) times cal(D)$ is a cartesian
    product of $cal(C)$ with $cal(D)$.
    
    Let us finally check that $cal(F)Cat$ is closed.  Consider $cal(C)$ and $cal(D)$ be two categories
    in $cal(F)Cat$, define $cal(D)^cal(C)$ be the category of $cal(F)$-continuous functors, with natural
    transformations as morphisms.  Since limits of shapes in $cal(F)$ exist in $cal(D)$, they exist in
    $cal(D)^cal(C)$.  Since limits are computed pointwise, the same proof that show that $Cat$ is closed
    works to show that $cal(D)^cal(C)$ is an internal hom.
]

#definition(title: [Shape functor])[
    There is a functor $
        -Cat &:& Shp^op &--> Cat \
            &&cal(F) &mapsto.long cal(F)Cat \
            &&cal(F) <= cal(F)' &mapsto.long cal(F)'Cat subset.eq cal(F)Cat
    $
]

Let $cal(F)$ be a complete set of shapes.  Let $cal(C) : cal(F)Cat$.  Consider $cal(F)$ as a
subcategory of $Cat$ whose morphisms are initial functors.  We can define, for $cal(S) : cal(F)$,
$[cal(S), cal(C)] : Cat$.  This defines a Grothendieck fibration: $ cal(F)^op -> Cat $

Let us define a functor $
    lim : integral_(cal(S) : cal(F)) [cal(S), cal(C)] --> cal(C)
$

The functor takes the diagram $cal(D) : cal(S) -> cal(C)$ to its limit $lim cal(D)$.  Let $phi :
cal(D) -> cal(D)'$ be a morphism, where $cal(D) : cal(S) -> cal(C)$ and $cal(D)' : cal(S)' -> cal(C)$.

Such morphism is a functor $phi_1 : cal(S) -> cal(S)'$, as well as a natural transformation
#align(center, diagram(spacing: (1cm, 2cm), $
    cal(S) edge("dr", cal(D), ->, label-side: #right) edge("rr", phi_1, ->) && cal(S)' edge("dl", cal(D)', ->, label-side: #left) \
        & cal(C)
$,
    edge((.8, .4), (1.4, .2), $phi_2$, "=>")
))

Let us define $lim phi : lim cal(D) -> lim cal(D)'$.  By initiality of $phi_1$, $lim cal(D)' tilde.equiv lim cal(D)' compose phi_1$ with a canonical isomorphism, so this is the same as defining a morphism $
    lim cal(D) --> lim cal(D)' compose phi_1
$

which is given by $lim phi_2$.

Let us check that this is a functor.  Clearly, the identity is mapped on the identity.  Furthermore,
suppose we have the following situation
#align(center, diagram(spacing: 2cm, $
    cal(S)_1 edge("r", phi_1, ->) edge("dr", cal(D)_1, ->, label-side: #right) 
        & cal(S)_2 edge("d", cal(D)_2, ->) edge("r", psi_1, ->)
        & cal(S)_3 edge("dl", cal(D)_3, ->, label-side: #left) \
        & cal(C)
$,
    edge((.6, .4), (.85,.15), $phi_2$, "=>"),
    edge((1.2, .4), (1.5, .25), $psi_2$, "=>"),
))

#theorem[
    Let $cal(F) <= cal(F)'$, the functor $(cal(F) <= cal(F)')Cat : cal(F)'Cat -> cal(F)Cat$ has a left
    adjoint.  Let us call this left adjoint $F^cal(F)'_cal(F) : cal(F)Cat -> cal(F)'Cat$.
]
#proof[
    See @beurier21:presen_clust_stric_free_cocom
    Let $cal(C)$ be a $cal(F)$-complete category.  Let us first show that we can freely add all limits
    of shape $cal(F)'$ in $cal(C)$.  Define $cal(hat(F))'$ be the greatest class of shapes equivalent to
    $cal(F)'$, that is, $
        cal(hat(F))' := union.big { cal(tilde(F)) : Shp | cal(tilde(F)) <= cal(F)' and cal(F)' <= cal(tilde(F)) }
    $  Consider the category $cal(C)_cal(F)'$, where objects are of the
    form $F : cal(S) -> cal(C)$ where $cal(S) : cal(hat(F))'$.  Intuitively, such a diagram represents its
    added limit in $cal(C)$.  Hence, we must have, for $F : cal(S) -> cal(C)$ and $G : cal(S)' -> cal(C)$, $
        cal(C)_cal(F)'(F, G) &:= lim_(s' : cal(S)') colim_(s : cal(S)) cal(C)(F(s), G(s'))
    $
    This is a category.  Indeed, for $F : cal(S) -> cal(C)$, we have an identity given by the following
    family of elements 
    
    #align(center, prooftree(
        rule(
            name: $-(*)$,
            rule(
                name: [$lim$-I],
                rule(
                    name: $- * iota$,
                    rule(
                        name: [nat],
                        rule(
                            name: [Id-I],
                            $* : 1, s : cal(S) entail_Set id_F(s) : cal(C)(F^op (s), F(s))$,
                        ),
                        rule(
                            $$,
                        ),
                        $* : 1 entail_(Set^cal(S)) id * F : cal(C)(F^op (-), F(-))$,
                    ),
                    $* : 1 entail_(Set^cal(S)) \_ : colim_(s : cal(S)) cal(C)(F^op (s), F(-))$,
                ),
                $* : 1 entail_Set \_ :  lim_(s' : cal(S)) colim_(s : cal(S)) cal(C)(F^op (s), F(s'))$,
            ),
            $entail_Set \_ : lim_(s' : cal(S)) colim_(s : cal(S)) cal(C)(F^op (s), F(s'))$,
        )
    ))
    
    $
        (s, id_F(s))_(s : cal(S)) in lim_(s : cal(S)) colim_(s : cal(S)) cal(C)(F(s), F(s))
    $
    
    Let $F_i : cal(S)_i -> cal(C)$ ($i : {1, 2, 3}$) be three objeccts of $cal(C)_cal(F)'$, and
    $f : F_1 -> F_2$ and $g : F_2 -> F_3$.  Let us build $g compose f : F_1 -> F_3$.  We must find
    an inhabitant of $
        lim_(s_3 : cal(S)_3) colim_(s_1 : cal(S)_1) cal(C)(F_1(s_1), F_3(s_3))
    $
    Let $s_3 : cal(S)_3$ we have, $g_s_3 = (s_2, alpha)$ with $alpha : cal(C)(F_2(s_2), F_3(s_3))$.
    We have $f_s_2 = (s_1, beta)$ avec $beta : cal(C)(F_1(s_1), F_2(s_2))$. We then have $
        (s_1, alpha compose beta) : colim_(s_3 : cal(S)_3) cal(C)(F_1(s_1), F_3(s_3))
    $
    Composing with the identity morphism gives the same morphism.
    
    Let now $cal(S) : cal(hat(F))'$ be a shape, and $F : cal(S) -> cal(C)_cal(F)'$ be a functor.
]

#proposition[
    For $cal(F) <= cal(F') <= cal(F)''$, we have $
        F_cal(F)''^cal(F) tilde.equiv F_cal(F)'^cal(F) compose F_cal(F)''^cal(F)'
    $
]
#proof[
    TODO
    this stems by uniqueness of left adjoints.
]

== $cal(F)$ theory
#definition(title: [$cal(F)$ theory])[
    A $cal(F)$ theory $cal(T)$ is an $cal(F)$-complete category.
]

A morphism of $cal(F)$ theory is simply a morphism of $cal(F)$-complete category.  In fact, there is
no technical distinction between the category of $cal(F)$ theories and $cal(F)Cat$.  However, in what
follows, we want to see those categories as _theories_, in the sense that they admit a (meta) theory of
models.

== Model of a $cal(F)$ theory
Let $cal(U) : cal(F)Cat$ be a category, called in this context a _universe_, and $cal(T)$ be a $cal(F)$
theory. 

#definition(title: [Model of a theory])[
    A _model M of $cal(T)$ in $cal(U)$_ is a morphism $cal(T) -> cal(U)$, that is, a functor that
    is continuous with respect to all limits of shapes in $cal(F)$.
]

#definition(title: [Morphism of models])[
    Given $M$ and $M'$ be two models of $cal(T)$, a _morphism from $M$ to $M'$_ is a natural 
    transformation $M => M'$.
]

#definition(title: [Category of models])[
    For a given theory $cal(T)$, we define its category of models (in $cal(U)$) $
        Mod_cal(T)(cal(U)) := cal(F)Cat(cal(T), cal(U))
    $
]

#remark[
    We are often primarily interested in models in $Set$ (which belongs to every $cal(F)$Cat).  
    However, being able to change the category in which we interpret are theory will be an
    other important tool to make compute describe theories later on.
]

== Monad on an $cal(F)$ theory
For this section, fix $cal(T)$ a $cal(F)$ theory, and $cal(U)$ be a universe, which has all limits
shaped by $cal(T)$.

#definition(title: [Free algebra monad])[
    Let us note $F_cal(T) : cal(U) -> cal(U)$ the monad on $cal(U)$ derived from the following
    adjunction
    #align(center, diagram(spacing: 2cm, $
        cal(U) edge("r", Delta, ->, shift: #8pt) & Mod_cal(T)(cal(U)) edge("l", lim, ->, shift: #8pt, label-side: #left)
    $,
        node((.4, 0), $bot$),
    ))
    which we call the _free algebra monad over $cal(U)$_.
]

#remark[
    If $cal(U)$ is complete, then in particular it has all limits of shape $cal(T)$, so we can always
    build the free algebra monad over it.
]
#example[
    $Set$ is complete.  Therefore, every theory induces a free algebra monad over the universe $Set$.
    We will see how to recover usual monads on $Set$ with this construction.
]

#proposition[
    The adjunction $Delta tack.l lim$ is monadic.
]
#proof[
    Consider the category $cal(U)^(F_cal(T))$ of algebras of the monad $F_cal(T)$.  There is a functor $
        G : Mod_cal(T)(cal(U)) --> cal(U)^(F_cal(T))
    $
    given by, for any element $M : Mod_cal(T)(cal(U))$, $
        (lim M, lim epsilon_M)
    $
    #margin-note[Finish this proof.]
]

#corollary[
    The category of algebras of the free algebra monad $F_cal(T)$ is isomorphic to the category of models
    of $cal(T)$.
]

= Quantifier-free first order logic
== Algebraic theories
For this section, we will consider categories with finite products, that is, $cal(F) = {0, 2}$.

#definition(title: [Multi-sorted Lawvere theory])[
    A $cal(F)$ theory $cal(T)$ is called a _multi-sorted Lawvere theory_.
]
#definition(title: [Category of models of $T$])[
    Given an algebraic theory $T$, its models, equiped with morphisms of models, form a category $Mod_T$
    of models of $T$.
]

== Horn theories

== Essentially algebraic theories

= Higher order logic
= Lawvere Theories
#definition(title: [Lawvere theory])[
    A _(generalized) Lawvere theory_ is a cartesian category.
]

#definition(title: [Model of a Lawvere theory])[
    A _model of a lawvere theory $cal(T)$ in a cartesian category $cal(C)$_ is a cartesian functor
    $M : cal(T) -> cal(C)$.
]

#definition(title: [Category of models of a Lawvere theory])[
    Given a Lawvere theory $cal(T)$, we define its _category of models $Mod_cal(T)(cal(C))$ in a cartesian
    category $cal(C)$_ as $
        Mod_cal(T)(cal(C)) = [cal(T), cal(C)]
    $
]

#definition(title: [Morphism of Lawvere theory])[
    Given two Lawvere theories $cal(T)$ and $cal(T)'$, a _morphism of Lawvere theories $cal(T) -> cal(T)'$_
    is a cartesian functor $F : cal(T) -> cal(T)'$.
]

#proposition[
    Given two Lawvere theories $cal(T)$ and $cal(T)'$, and a morphism $F : cal(T) -> cal(T)'$.  Let $cal(C)$
    be a cartesian category.  There exists a cartesian functor $Mod_F (cal(C)) : Mod_cal(T)'(cal(C)) -> 
    Mod_cal(T)(cal(C))$.
]
#proof[
    Let $M : cal(T)' -> cal(C)$, we have $M compose F : cal(T) -> cal(C)$.  Furthermore, given a natural
    transformation $alpha : M_1 -> M_2$, we have $
        alpha * F : M_1 compose F -> M_2 compose F
    $
    which is functorial: $id_M * F = id_(M compose F)$ and $(alpha compose beta) * F = (alpha * F) compose
    (beta * F)$.
    
    Let $M_1, M_2 : cal(T) -> cal(C)$ be two models.  $(M_1 times M_2) compose F = (M_1 compose F) times 
    (M_2 compose F)$ by definition, since limits are computed pointwise.  Similarly, $pi_i * F = pi_i : (M_1 
    compose F) times (M_2 compose F) -> M_i compose F$.
]

#proposition[
    $Mod_-(cal(C)) : CCat^op -> CCat$ est un foncteur contravariant continu.
]
#proof[
    C'est exactement le foncteur $CCat(-, cal(C))$, c'est donc bien un foncteur contravariant, et il est
    bien continu.
]

#example[
    Consider an algebraic theory $T$.  We can build its Lawvere theory $cal(T)$ as follows:
    objects of $cal(T)$ are words of $S$, noted $s_1 times dots.c times s_n$.  A morphism from a
    $product_(i = 1)^n s_i -> product_(i = 1)^m s'_i$ is a tuple $(t_1, ..., t_m)$ where each $t_i$ is a
    term in the context $Gamma := x_1 : s_1, ..., x_n : s_n$ on the language $cal(L)$, quotiented by the
    equivalence relation $t_i ~ t'_i$ if $T tack t_i = t'_i$.
    
    We have an important result: $
        Mod_cal(T)(Set) tilde.equiv Mod_T
    $
]

#theorem[
    Consider $cal(T)_1$ and $cal(T)_2$ two Lawvere theories.  A $cal(T)_1$-model in the category of
    $cal(T)_2$-models is the same thing as a $cal(T)_2$-model in the category of $cal(T)_1$-models.
    In fact, there is a (natural) isomorphism, for any cartesian category $cal(C)$, $
        Mod_cal(T)_1(Mod_cal(T)_2(cal(C))) tilde.equiv Mod_cal(T)_2(Mod_cal(T)_1(cal(C)))
    $
]
#proof[
]

#theorem[
    Two Lawvere theories $cal(T)_1$ and $cal(T)_2$ such that, for any cartesian category $cal(C)$,
    $Mod_cal(T)_1(cal(C)) tilde.equiv Mod_cal(T)_2(cal(C))$ naturally in $cal(C)$, then $cal(T)_1 
    tilde.equiv cal(T)_2$.
]
#proof[
    This stems directly from the Yoneda lemma.
]

#set heading(supplement: none)
#bibliography("categorical-semantics-of-logic.bib")

// Local Variables:
// typst-preview--master-file: "./categorical-semantics-of-logic.typ"
// End:
