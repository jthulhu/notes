#import "common.typ": *

#let yo = [*y*]
#let Cat = [*Cat*]
#let Set = [*Set*]

#show: all.with([Notes on Natural Models of HoTT], none)

= Yoneda Lemma

For this section, $cal(C)$ is a locally small category.  The goal of this section is to prove the
Yoneda lemma.

#definition(title: [Yoneda embedding])[
    Let us define the Yoneda embedding $yo : cal(C) arrow hat(cal(C))$ by
    - for $X : cal(C)$ an object, $yo(C) : cal(C)^op &arrow Set$ is defined by
      $yo(X)(Y)= cal(C)(Y, X)$ for any object $Y : cal(C)$, and for a morphism $f : Y arrow Z$ in $cal(C)$,
      $
          yo(X)(f) &:& yo(X)(Z) &arrow yo(X)(Y) \
              && g &mapsto g compose f
      $
      which is indeed functorial;
    - for $f : X arrow Y$ a morphism, $yo(f) : yo(X) arrow yo(Y)$ is defined, for $Z : cal(C)^op$, by$
        yo(f)_Z &:& yo(X)(Z) &arrow yo(Y)(Z) \
            && g &mapsto f compose g
      $
      which is functorial.
      
]

#theorem(title: [Yoneda lemma])[
    Let $F$ be a presheaf over $cal(C)$, and $X : cal(C)$ be a object. We have that $
        hat(cal(C))(yo(X), F) tilde.equiv F(X)
    $
    Furthermore, the isomorphism is natural in $F$ and $X$.
]
#proof[
    Let $theta : yo(X) arrow F$ be a natural transformation.  $theta_X (id_X) in F(X)$, so we can
    define $
        psi_(X, F) &:& hat(cal(C))(yo(X), F) &arrow.long F(X) \
            && theta &mapsto.long theta_X (id_X)
    $
    Let's now show that $psi_(X, F)$ is a bijection, by showing that it is both injective and
    surjective.  Let $theta : yo(X) arrow F$ be a natural transformation, and $f : Y arrow X$ be
    a morphism in $cal(C)$.  The following diagram commutes
    #align(center, diagram($
        yo(X)(X) edge("r", theta_Z, ->) edge("d", yo(X)(f), ->) & F(X) edge("d", F(f), ->) \
        yo(X)(Y) edge("r", theta_Y, ->) & F(Y)
    $))
    so $
        theta_Y (f) = F(f)(psi_(X, F)(theta))
    $
    which proves that $theta$ is uniquely determined by $psi_(X, F)(theta)$, and defines it entirely.
]

// Local Variables:
// tp--master-file: "./natural-models-of-homotopy-type-theory.typ"
// End:
