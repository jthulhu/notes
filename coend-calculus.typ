#import "common.typ": *
#import "@preview/tiptoe:0.4.0" as tiptoe: line
#import "@preview/xarrow:0.4.0": xarrow
#show: all.with([Notes on (Co)end Calculus], none)

#let Set = [*Set*]
#let Cat = [*Cat*]
#let Top = [*Top*]
#let ff = [ff]
#let tt = [tt]
#let Sub = [Sub]
#let Orb = [Orb]
#let Gal = [Gal]
#let copsi = [⋔]
#let Type = [*Type*]
#let ev = [ev]
#let dinat = {
    box(baseline: -1.75pt, stack(
        dir: ttb,
        spacing: 2pt,
        line(length: 1em, stroke: .6pt),
        line(length: 1em, stroke: .6pt),
    ))
    h(-1.5pt)
    math.diamond.small
}

= Dinaturality and co/ends
#exercise[
    Prove equations (1.5) and (1.6), that is, for a morphism $f : B -> B'$ and $u : A -> X^B'$, $
        epsilon.alt_(X, B') compose (u times B') compose (A times f)
            &= epsilon.alt_(X, B) compose (X^f compose u) times B
            & quad & (1.5) \
            epsilon.alt_(X, B') compose (X^B' times f) compose (u times B)
            &= epsilon.alt_(X, B) compose (X^f times B) compose (u times B)
            & & (1.6)
    $
]
#proof[
    Naturality in $B$ of the isomorphism $Set(A, X^B) tilde.equiv Set(A times B, X)$ states
    that the following diagram commutes
    #align(center, diagram(spacing: 2cm, $
        Set(A, X^B') edge("r", ev_(A,X,B'), ->) edge("d", Set(A, X^f), ->)
            & Set(A times B', X) edge("d", Set(A times f, X), ->) \
            Set(A, X^B) edge("r", ev_(A, X, B), ->) & Set(A times B, X)
    $))
    hence
    $
        (Set(A times f, X) compose ev_(A, X, B'))(u) = (ev_(A,X,B) compose Set(A, X^f))(u)
    $
    where $ev_(A, X, B')(u) = epsilon.alt_(X, B') compose (u times B')$
    Thus
    #align(center, diagram(spacing: 2cm, $
        A times B edge("r", A times f) edge("dd", (X^f compose u) times B, ->)
            & A times B' edge("d", u times B') \
            & X^B' times B' edge("d", epsilon.alt_(X, B'), ->) \
            X^B times B edge("r", epsilon.alt_(X, B), ->) & X
    $))
    which is exactly equation (1.5).

    (1.6) follows immediately from (1.5) as $(X^f compose u) times B = (X^f times B) compose (u times B)$
    and $(u times B') compose (A times f) = (X^B' times f) compose (u times B)$, by functoriality of
    $- times -$.
]

#exercise[
    + For $cal(C)$ and $cal(D)$ two categories, and $P, Q, R : cal(C)^op times cal(C) -> cal(D)$
      functors, show with an example that dinatural transformations $alpha : P dinat Q$ and
      $beta : Q dinat R$ cannot be composed in general.
    + Show, however, that dinatural transformations and natural transformations can be composed
      to form dinatural transformations.
]
#proof[
    + Consider $cal(C) = bold(2)$, and $cal(D) = {bb(B)}$ be a full subcategory of #Set.
      Let $
          P &:& bold(2)^op times bold(2) &arrow.long {bb(B)} \
              && (x, y) &mapsto.long bb(B) \
              && (f, g) &mapsto.long lambda x. ff
      $
      and $Q = P$.  Let $
          alpha &:& P &dinat Q \
              && x &mapsto.long not -
      $
      This is a dinatural transformation.  Indeed consider the following dinaturality condition
      diagram at $0 < 1$
      #align(center, diagram(spacing: 2cm, $
          & bb(B) edge("dl", ff, ->) edge("dr", ff, ->) \
          bb(B) edge("d", not -, ->) & & bb(B) edge("d", not -, ->) \
          bb(B) edge("dr", ff, ->) & & bb(B) edge("dl", ff, ->) \
              & bb(B)
      $))
      It clearly commutes.
      Now, consider $
          R &:& cal(bold(2))^op times cal(bold(2)) &arrow.long {bb(B)} \
              && (x, y) &mapsto.long bb(B) \
              && (0 < 1, id) &mapsto.long id_bb(B) \
              && (id, 0 < 1) &mapsto.long lambda x. ff
      $
      and have $beta : Q dinat R$ be identity pointwise.  $beta$ is a dinatural transformation.
      Indeed consider the following dinaturality condition diagram at $0 < 1$
      #align(center, diagram(spacing: 2cm, $
          & bb(B) edge("dl", ff, ->) edge("dr", ff, ->) \
          bb(B) edge("d", id_bb(B), ->) & & bb(B) edge("d", id_bb(B), ->) \
          bb(B) edge("dr", ff, ->) & & bb(B) edge("dl", id_bb(B), ->) \
              & bb(B)
      $))
      Again, this clearly commutes.  Yet, the compositioin $beta compose alpha$ is not a
      dinatural transformation, as can be witnessed by looking the dinaturality condition
      diagram at $0 < 1$
      #align(center, diagram(spacing: 2cm, $
          & bb(B) edge("dl", ff, ->) edge("dr", ff, ->) \
          bb(B) edge("d", not -, ->)
              & bb(B) edge("dl", ff, ->) edge("dr", ff, ->)
              & bb(B) edge("d", not -, ->) \
              bb(B) edge("d", id_bb(B), ->) edge("dr", ff, ->)
              & & bb(B) edge("dl", ff, ->) edge("d", id_bb(B), ->) \
              bb(B) edge("dr", ff, ->)
              & bb(B)
              & bb(B) edge("dl", id_bb(B), ->) \
              & bb(B)
      $))
      which does not commute: the left morphism is the constant $ff$ morphism, while the right one is
      the constant $tt$ morphism.
    + Consider $alpha : P dinat Q$ be a dinatural transformation, and $beta : Q => R$ be a natural
      transformation.
      Let $(beta compose alpha)_C = beta_(C, C) compose alpha_C$.  Let us check that this indeed forms
      a dinatural transformation.  Let $f : C -> C'$ be a morphism in $cal(C)$.
      The following diagram commutes, as the upper hexagon commutes by dinaturality of $alpha$,
      and the two lower squares commute by naturality of $beta$
      #align(center, diagram(spacing: 2cm, $
          & P(C', C) edge("dl", P(f, C), ->) edge("dr", P(C', f), ->) \
          P(C, C) edge("d", alpha_C, ->) & & P(C', C') edge("d", alpha_C', ->) \
          Q(C, C) edge("dr", Q(C, f), ->) edge("d", beta_(C, C), ->)
              & & Q(C', C') edge("d", beta_(C', C'), ->) edge("dl", Q(f, C'), ->) \
              R(C, C) edge("dr", R(C, f), ->, label-side: #right)
              & Q(C, C') edge("d", alpha_(C, C'), ->)
              & R(C', C') edge("dl", R(f, C'), ->, label-side: #left) \
              & R(C, C')
      $))

      Consider now a natural transformation $alpha : P => Q$ and a dinatural transformation
      $beta : Q dinat R$.  Let $(beta compose alpha)_C = beta_C compose alpha_(C, C)$.  Let us
      check that this indeed forms a dinatural transformation.  Let $f : C -> C'$ be a morphism
      in $cal(C)$.
      The following diagram commutes, as the lower hexagon commutes by dinaturality of $beta$,
      and the upper squares commute by naturality of $alpha$.
      #align(center, diagram(spacing: 2cm, $
          & P(C', C) edge("dl", P(f, C), ->) edge("dr", P(C', f), ->) edge("d", alpha_(C', C), ->) \
          P(C, C) edge("d", alpha_(C, C), ->)
              & Q(C', C) edge("dl", Q(f, C), ->) edge("dr", Q(C', f), ->)
              & P(C', C') edge("d", alpha_(C', C'), ->) \
              Q(C, C) edge("d", beta_C, ->) & & Q(C', C') edge("d", beta_C', ->) \
              R(C, C) edge("dr", R(C, f), ->) & & R(C', C') edge("dl", R(f, C'), ->) \
              & R(C, C')
      $))
]

#exercise(breakable: false)[
    Let $cal(C)$ and $cal(D)$ be two non-empty categories, and $D : cal(D)$ be an object of $cal(D)$.
    + compute $integral_(C : cal(C)) D$
    + compute $integral^(C : cal(C)) D$
]
#proof[
    + Consider an other object $X$ with $alpha : X dinat D$.  For any two objects $C C' : cal(C)$, and
      a morphism $f : C -> C'$, we have
      have $alpha_C = alpha_C'$ from the commutation of this diagram
      #align(center, diagram(spacing: 2cm, $
          & X edge("dl", id_X, ->) edge("dr", id_X, ->) \
          X edge("d", alpha_C, ->) & & X edge("d", alpha_C', ->) \
          D edge("dr", id_D, ->) & & D edge("dl", id_D, ->) \
              & D
      $))
      $alpha$ is therefore constant on each connected component of $cal(C)$,
      hence, if we denote by $c(cal(C))$ the connected components of $cal(C)$, we have, if the end
      exists,
      $
          cal(D)(X, integral_(C : cal(C)) D) &tilde.equiv cal(D)(c(cal(C)) times.o X, D) \
              &tilde.equiv cal(D)(X, D)^(c(cal(C))) \
              &tilde.equiv cal(D)(X, c(cal(C)) copsi D)
      $
      and hence, by the Yoneda lemma, we find out that we must have $
          integral_(C : cal(C)) D = c(cal(C)) copsi D
      $
      The proof of this is easy: consider the wedge $c(cal(C)) copsi D$ and $alpha : c(cal(C)) copsi D dinat D$
      defined, as shown earlier, on each connected component $s : c(cal(C)) copsi D$ by $
          alpha_s = pi_s
      $
      The rest is immediate, by noting that $integral_(C : cal(C)) D$ has the same universal property as
      $c(cal(C)) copsi D$.
    + By the same argument as above, a cowedge on $D$ is the same thing as an object $X$ and, for each
      connected component $s : c(cal(C))$, a morphism $alpha_s : D -> X$.  Hence
      $
          cal(D)(integral^(C : cal(C)) D, X) &tilde.equiv cal(D)(D, s(cal(C)) copsi X) \
              &tilde.equiv cal(D)(c(cal(C)) times.o D, X)
      $
      and thus $
          integral^(C : cal(C)) D = c(cal(C)) times.o D
      $
]

#exercise(breakable: false)[
    Show that extranatural transformations compose accordingly to these rules:
    - (stalactites) Let $F, G : cal(C)^op times cal(C) -> cal(D)$ be functors.  If $alpha : F => G$
      is a natural transformation, and $beta_X : G(X, X) -> H$ is extranatural in $X$ (for some
      $H : cal(D)$), then $
          beta_X compose alpha_(X,X) : F(X, X) -> H
      $
      is extranatural in $X$.
    - (stalagmites) Let $G, H : cal(C)^op times cal(C) -> cal(D)$.  If $alpha_X : F -> G(X, X)$ is
      extranatural in $X$ (for some object $F : cal(D)$), and $beta : G => Y$ is a natural
      transformation, then $
          beta_(X,X) compose alpha_X : F -> H(X,X)
      $
      is extranatural in $X$.
    - (yanking) Let $F, H : cal(C) -> cal(D)$, and let $G : cal(C) times cal(C)^op times cal(C) -> cal(D)$
      be a functor.  If $alpha_(X, Y) : F(Y) -> G(X, X, Y)$ is natural in $Y$ and extranatural in
      $X$, and if $beta_(X, Y) : G(X, Y, Y) -> H(X)$ is natural in $X$ and extranatural in $Y$, then
      $
          beta_(X,X) compose alpha_(X, X) : F(X) -> H(X)
      $
      is natural in $X$.
    Express these laws as equalities between suitable string diagrams (explaining also the
    genesis of the names 'stalactite' and 'stalagmite').
]
#proof[
    - We only need to check a single commutativity diagram: let $X, X' : cal(C)$, and $f : X -> X'$
      a morphism in $cal(C)$
      #align(center, diagram(spacing: 2cm, $
          F(X', X) edge("rr", F(X', f), ->) edge("d", F(f, X), ->) edge("dr", alpha_(X', X), ->)
              && F(X', X') edge("d", alpha_(X', X'), ->) \
              F(X, X) edge("d", alpha_(X, X), ->)
              & G(X', X) edge("dl", G(f, X), ->) edge("r", G(X', f), ->)
              & G(X', X') edge("d", beta_X', ->) \
              G(X, X) edge("rr", beta_X, ->)
              && H
      $))
      The upper-right square commutes by naturality of $alpha$, the left one too, and the
      lower-right square commutes by extranaturality.
    - Again, we only need to check a single commutativity diagram: let $X, X' : cal(C)$ and
      $f : X -> X'$ a morphism
      #align(center, diagram(spacing: 2cm, $
          F edge("rr", alpha_X, ->) edge("d", alpha_X', ->)
              && G(X, X) edge("d", beta_(X, X), ->) edge("dl", G(X, f), ->) \
              G(X', X') edge("d", beta_(X', X'), ->) edge("r", G(f, X'), ->)
              & G(X, X') edge("dr", beta_(X, X'), ->)
              & Y(X, X) edge("d", Y(X, f), ->) \
              Y(X', X') edge("rr", Y(f, X'), ->) && Y(X, X')
      $))
      the upper-left square commutes by extranaturality of $alpha$, while the lower-left and
      rightmost squares commute by naturality of $beta$.
    - Let $X, X' : cal(C)$ be two objects, and $f : X -> X'$ a morphism between them.
      #align(center, diagram(spacing: 2cm, $
          F(X) edge("rr", F(f), ->) edge("d", alpha_(X, X), ->)
              && F(X') edge("d", alpha_(X', X'), ->) edge("dl", alpha_(X, X'), ->) \
              G(X, X, X) edge("dddd", beta_(X, X), ->) edge("r", G(X, X, f), ->)
              edge("ddr", G(f, X, X), ->, label-side: #right)
              & G(X, X, X') edge("d", G(f, X, X'), ->)
              & G(X', X', X') edge("dddd", beta_(X', X'), ->) edge("dl", G(X', f, X'), ->) \
              & G(X', X, X') \
              & G(X', X', X) edge("d", G(X', f, X), ->, label-side: #left)
              edge("uur", G(X', X', f), ->, label-side: #right) \
              & G(X', X, X) edge("dr", beta_(X', X), ->) \
              H(X) edge("rr", H(f), ->)
              && H(X')
      $))
]

#exercise(breakable: false)[
    Prove that dinaturality is strictly more general than extranaturality.
]
#proof[
    Let $cal(2)$ be the walking arrow category, and $S, T : cal(2)^op times cal(2) -> Set$ be
    defined by
    #grid(
        columns: (1fr, 1fr, 1fr),
        align: center + horizon,
        diagram(spacing: 1cm, $
            {1} edge("r", c_1, ->) edge("d", id_{1}, ->) & {1, 2} edge("d", sigma, ->) \
            {1} edge("r", c_2, ->, label-side: #right) & {1, 2}
        $,
            node((.5, .5), $S$),
        ),
        diagram(spacing: 1cm, $
            (1, 0) edge("r", ->) edge("d", ->) & (1, 1) edge("d", ->) \
            (0, 0) edge("r", ->) & (0, 1)
        $),
        diagram(spacing: 1cm, $
            {1} edge("d", id_{1}, ->) edge("r", id_{1}, ->) & {1} edge("d", c_2, ->) \
            {1} edge("r", c_2, ->, label-side: #right) & {1, 2}
        $,
            node((.5, .5), $T$),
        ),
    )
    where $c_i$ is the constant function at $i$, at $sigma : {1, 2} -> {1, 2}$ is the
    non-trivial permutation.

    Consider the transformation
    $
        alpha &:& T &dinat S \
            && 0 &mapsto.long id_{1} \
            && 1 &mapsto.long {1} subset.eq {1, 2}
    $
    it is dinatural, as the following diagram clearly commutes
    #align(center, diagram(spacing: 2cm, $
        & T(1, 0) = {1} edge("dl", T(1 > 0, 0) = id_{1}, ->) edge("dr", T(1, 0 < 1) = id_{1}, ->) \
        T(0, 0) = {1} edge("d", alpha_0 = id_{1}, ->)
            & & T(1, 1) = {1} edge("d", alpha_1 = {1} subset.eq {1, 2}, ->) \
            S(0, 0) = {1} edge("dr", S(0, 0 < 1) = c_2, ->, label-side: #right)
            & & S(1, 1) = {1, 2} edge("dl", S(0 < 1, 1) = sigma, ->, label-side: #left) \
            & S(0, 1) = {1, 2}
    $))

    Yet, it is not extranatural if we see it as a transformation $T => S$ where
    $T : bold(1) times bold(2)^op times bold(2) -> Set$ and
    $S : bold(1) times bold(2) times bold(2)^op -> Set$.
    Indeed, assume it is, then take $B = 0$, $B' = 1$ and $C = 1$.  We have
    #align(center, diagram(spacing: 2cm, $
        T(1, 0) = {1} edge("r", T(1, 0 < 1) = id_{1}, ->) edge("d", T(1 > 0, 0) = id_{1}, ->)
            & T(1, 1) = {1} edge("d", alpha_1 = {1} subset.eq {1, 2}, ->) \
            T(0, 0) = {1} edge("r", alpha_(0, 1), ->) & S(1, 1) = {1, 2}
    $))
    So $alpha_(0, 1) = {1} subset.eq {1, 2} $.
    Let's now take $B = 0$, $C = 0$ and $C' = 1$.
    #align(center, diagram(spacing: 2cm, $
        T(0, 0) = {1} edge("d", alpha_(0, 1) = {1} subset.eq {1, 2}, ->) edge("r", alpha_0 = id_{1}, ->)
            & S(0, 0) = {1} edge("d", S(0, 0 < 1) = c_2, ->) \
            S(1, 1) = {1, 2} edge("r", S(1 < 0, 1) = sigma, ->) & S(0, 1) = {1, 2}
        
    $))
]

#exercise(breakable: false)[
    Let $n : bb(N)$, and, for $i : {1, ..., n}$, $cal(A)_i$ be a category with an initial and
    a terminal object.  Let $cal(C)$ be a category, and $F : cal(C)^op times cal(C) ->
    product_(i = 1)^n cal(A)_i$ be a functor such that every $integral_C pi_i (F(C, C))$ (resp.
    $integral^C pi_i (F(C, C))$) exists.  Show that $
        integral_C F(C, C) = (integral_C pi_1 (F(C, C)), ..., integral_C pi_n (F(C, C)))
    $
    resp. $
        integral^C F(C, C) = (integral^C pi_1 (F(C, C)), ..., integral^C pi_n (F(C, C)))
    $
]
#proof[
    Let $cal(A) = product_(i = 1)^n cal(A)_i$, $i : {1, ..., n}$, $X : cal(A)_i$ and $hat(X) = (0, ..., X, ..., 0)$.
    $
        cal(A)_i (X, pi_i (integral_C F(C, C))) &tilde.equiv cal(A)(hat(X), integral_C F(C, C)) \
            &tilde.equiv integral_C cal(A)(hat(X), F(C, C)) \
            &tilde.equiv integral_C cal(A)_i (X, pi_i (F(C, C))) \
            &tilde.equiv cal(A)_i (X, integral_C pi_i (F(C, C)))
    $
    Thus, by the Yoneda lemma, we have $
        pi_i (integral_C F(C, C)) tilde.equiv integral_C pi_i (F(C, C))
    $
    and thus $
        integral_C F(C, C) tilde.equiv (integral_C pi_1 (F(C, C)), ..., integral_C pi_n (F(C, C)))
    $
]

#exercise(breakable: false)[
    Let $cal(D)$ be a category.  Show that the end of a functor T : $Delta[1]^op times Delta[1] -> cal(D)$
    is the following pullback
    #align(center, diagram(spacing: 2cm, $
        integral_(i : Delta[1]) T(i, i) edge("d", ->) edge("r", ->)
            & T(0, 0) edge("d", T(0, 0 < 1), ->) \
            T(1, 1) edge("r", T(1 > 0, 0), ->) & T(0, 1)
    $))
]
#proof[
    Firstly, the diagram commutes by definition of a wedge.  Consider now $X : cal(D)$ with 
    $f : X -> T(1,1)$ and $g : X -> T(0, 0)$ such that the following diagram commutes
    #align(center, diagram(spacing: 2cm, $
        X edge("drr", g, ->, bend: #20deg) edge("ddr", f, ->, bend: #(-20deg)) \
            & integral_(i : Delta[1]) T(i, i) edge("r", ->) edge("d", ->) 
            & T(0, 0) edge("d", T(0, 0 < 1), ->) \
            & T(1, 1) edge("r", T(1 > 0, 0) ->) & T(0, 1)
    $))
    This defines exactly a wedge $alpha : X dinat T$, where $alpha_0 = g$ and $alpha_1 = f$.
    Hence, there exists a unique $phi : X -> integral_i T(i, i)$ making the following diagram commute
    #align(center, diagram(spacing: 2cm, $
        X edge("dr", "=<>") edge("rr", phi, ->, "dashed") && integral_(i : Delta[1]) T(i, i) edge("dl", "=<>") \
            & T
    $))
    That is, the following diagram commutes
    #align(center, diagram(spacing: 2cm, $
        X edge("drr", g, ->, bend: #20deg) edge("ddr", f, ->, bend: #(-20deg)) edge("dr", phi, ->, "dashed") \
            & integral_(i : Delta[1]) T(i, i) edge("r", ->) edge("d", ->) 
            & T(0, 0) edge("d", T(0, 0 < 1), ->) \
            & T(1, 1) edge("r", T(1 > 0, 0) ->) & T(0, 1)
    $))
]

#exercise[
    Let $G$ be a topological group, and $Sub(G)$ the set of its subgroups partially ordered by inclusion;
    let $X$ be a $G$-space, i.e. a topological space with a continuous action $X times X -> X$.
    
    We can define two functors $Sub(G) -> Top$, sending $(H <= G) mapsto G \/ H$ (this is a covariant functor,
    and $G \/ H$ has the induced quotient topology as a space; there is no need for $H$ to be normal) and
    $(H <= G) mapsto X^H$ (the sub of $H$-fixed points for the action; this is a contravariant
    functor).
    - Compute the coend $
        frak(o)_G (X) = integral^(H <= G) X^H times G \/ H
      $
      in the category $Top$ of topological spaces, if $G = bb(Z) \/ 2$ has the discrete topology.
    - Give a general rule for computing $frak(o)_G (X)$ when $G = bb(Z)\/n bb(Z)$ is cyclic with
      $n$ elements.
    - Let instead $Orb(G)$ be the _orbit category_ of subgroups of $G$, whose objects are subgroups
      but $hom(H, K)$ contains _$G$-equivariant_ maps $G\/H -> G\/K$.  Let again $X^-$ and $G \/ -$
      define the same functors, now with different action on arrows.  Prove that $
          integral^(H : Orb(G)) X^H times G \/ H tilde.equiv X
      $
    - Let $E|F$ be a field extension, and ${H <= Gal(E|F)}$ the partially
      ordered set of subgroups of the Galois group of extensions.  Compute (in the category
      of _rings_) the coend $
          integral^H E^H times Gal(H|F)
      $
]

#exercise[
    Dualise the construction in 1.2, to obtain a characterisation for the coend $integral^C F(C, C)$,
    characterised as the coequaliser of a pair $(F^*, F_*)$ as in $
        product.co_(C -> C') F(C', C) arrows product.co_(C : cal(C)) F(C, C) 
    $
]

#exercise[
    Find an alternative proof that natural transformations can be written as an end (see 1.4.1),
    using the characterisation of $integral_C cal(D)(F(C), G(C))$ as an equliser in 1.2.4: as a
    subset of $product_(C : cal(C)) cal(D)(F C, G C)$, is precisely the subset of natural 
    transformations ${tau_C : F C -> G C | forall f : C -> C', G f compose tau_C = tau_C' compose F f}$
]

#exercise[
    What is the co/end of the identity functor $
        integral_C (C, C) quad quad integral^C (C, C)
    $
    Use the bare definition.  Use the characterisation of co/ends as co/limits; feel free to
    invoke Exercise 1.6.
]

#exercise[
    A set of objects $S subset C$ regarded as a full subcategory, _finitely generates_ a category
    $cal(C)$ if for each object $X : cal(C)$, and each arrow $f : S -> C$ from $S : cal(S)$ there
    is a factorisation $
        S xarrow(g) product.co_(i = 1)^n S_i xarrow(h_C) C
    $
    where $h_C$ is an epimorphism and ${S_1, ..., S_n} subset cal(S)$ ($n$ depends on $C$ and $f$).
    
    Suppose $T : cal(C)^op times cal(C) -> Set$ is a functor, finitely continuous in both
    variables, and $cal(C)$ is finitely generated by $S$.  Then if we denote $T|_cal(S) : cal(S)^op 
    times cal(S) -> Set$ the restriction, we have an isomorphism $
        integral^(C : cal(S)) T|_cal(S) (C, C) tilde.equiv integral^(C : cal(C)) T(C, C)
    $
    induced by a canonical arrow $
        integral^(C : cal(S)) T'(C, C) --> integral^(C : cal(C)) T(C, C)
    $
]

#exercise[
    Let $F tack.l U : cal(C) arrows.lr cal(D)$ be an adjunction, and $G : cal(D)^op times cal(C) -> cal(E)$
    a functor; then there is an isomorphism $
        integral^C G(F C, C) tilde.equiv^D G(G, U D)
    $
    Show that the converse of this result is true: if the above ismorphism is true for any $G$ and
    natural therein, then there is an adjunction $F tack.l U$.
]

#exercise[
    
]

// Local Variables:
// typst-preview--master-file: "./coend-calculus.typ"
// End:
