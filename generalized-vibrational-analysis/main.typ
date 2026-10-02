#set par(justify: true)
#show link: underline
#import "@preview/physica:0.9.7"
#set math.equation(numbering: "(1)", number-align: bottom)
#let hfrac(a, b) = math.frac(a, b, style: "horizontal")
#let sfrac(a, b) = math.frac(a, b, style: "skewed")

// Define "Proposition" block
#show figure.where(kind: "prop"): set figure.caption(position: top)
#show figure.where(kind: "prop"): set align(start)
#show figure.caption.where(kind: "prop"): it => [
  #set text(size: 10pt)
  *#it.supplement #context it.counter.display(it.numbering).* #it.body
]
#let proposition(statement, title: none, proof: none) = figure(
  kind: "prop",
  supplement: [Proposition],
  caption: [
    #set math.equation(numbering: none)
    #if title != none [_*#title.*_]#if proof != none [#footnote[_Proof:_ #proof]]
    _ #statement _
  ],
  [#h(100%)]
)


= Generalized Vibrational Analysis

== Notation

#table(
  columns: (auto, auto),
  stroke: none,
  $q^mu$, [Cartesian displacement coordinate, $q^mu = x^mu - x^mu_0$],
  $g_mu$, [Cartesian gradient, $g_mu = physica.pdv(V, q^mu) = physica.pdv(V, x^mu)$],
  $H_(mu nu)$, [Cartesian Hessian, $H_(mu nu) = physica.pdv(V, q^mu, q^nu) = physica.pdv(V, x^mu, x^nu)$],
  $bold(v), bold(w)$, [Cartesian vectors with components $v^mu$, $w^mu$],
  $bold(alpha), bold(beta)$, [Cartesian co-vectors with components $alpha_mu$, $beta_mu$],
  $bold(v)^flat$, [Dual (lowered) Cartesian co-vector with components $v_mu = G_(mu nu) v^nu$],
  $bold(alpha)^sharp$, [Dual (raised) Cartesian vector with components $alpha^mu = G^(mu nu) alpha_nu$],
  [$G_(mu nu)$ and $G^(mu nu)$], [Co- and contravariant Cartesian coordinate metrics],
  $physica.iprod(bold(v), bold(w))$, [Cartesian vector inner product, $physica.iprod(bold(v), bold(w)) = G_(mu nu) v^mu w^nu$],
  $physica.iprod(bold(alpha), bold(beta))$, [Cartesian co-vector inner product, $physica.iprod(bold(alpha), bold(beta)) = G^(mu nu) alpha_mu beta_nu$],
  $tilde(q)^mu$, [Mass-weighted Cartesian displacement coordinate, $tilde(q)^mu = m_((mu))^(1/2) q^mu$],
  $tilde(g)_mu$, [Mass-weighted Cartesian gradient, $tilde(g)_mu = physica.pdv(V, tilde(q)^mu) = m_((mu))^(-1/2) physica.pdv(V, q^mu)$],
  $tilde(H)_(mu nu)$, [Mass-weighted Cartesian Hessian, $tilde(H)_(mu nu) = physica.pdv(V, tilde(q)^mu, tilde(q)^nu) = m_((mu))^(-1/2) m_((nu))^(-1/2) physica.pdv(V, q^mu, q^nu)$],
  $bold(tilde(v)), bold(tilde(w))$, [Mass-weighted Cartesian vectors with components $tilde(v)^mu$, $tilde(w)^mu$],
  $bold(tilde(alpha)), bold(tilde(beta))$, [Cartesian co-vectors with components $tilde(alpha)_mu$, $tilde(beta)_mu$],
  [$tilde(G)_(mu nu)$ and $tilde(G)^(mu nu)$], [Co- and contravariant mass-weighted Cartesian coordinate metrics],
  $physica.iprod(bold(tilde(v)), bold(tilde(w)))$, [Cartesian vector inner product, $physica.iprod(bold(tilde(v)), bold(tilde(w))) = tilde(G)_(mu nu) tilde(v)^mu tilde(w)^nu$],
  $physica.iprod(bold(tilde(alpha)), bold(tilde(beta)))$, [Cartesian co-vector inner product, $physica.iprod(bold(tilde(alpha)), bold(tilde(beta))) = tilde(G)^(mu nu) tilde(alpha)_mu tilde(beta)_nu$],
  $q^i$, [Internal displacement coordinate],
  $g_i$, [Internal coordinate gradient, $g_i = physica.pdv(V, q^i)$],
  $H_(i j)$, [Internal coordinate Hessian, $H_(i j) = physica.pdv(V, q^i, q^j)$],
  $bold(v)', bold(w)'$, [Internal coordinate vectors with components $v^i$, $w^i$],
  $bold(alpha)', bold(beta)'$, [Internal coordinate co-vectors with components $alpha_i$, $beta_i$],
  [$G_(i j)$ and $G^(i j)$], [Co- and contravariant Cartesian coordinate metrics],
  $physica.iprod(bold(v)', bold(w)')$, [Internal coordinate vector inner product, $physica.iprod(bold(v)', bold(w)') = G_(i j) v^i w^j$],
  $physica.iprod(bold(alpha)', bold(beta)')$, [Internal coordinate co-vector inner product, $physica.iprod(bold(alpha)', bold(beta)') = G^(i j) alpha_i beta_j$],
  $B^i_mu$, [Internal coordinate Jacobian with respect to Cartesians,
  $B^i_mu equiv physica.pdv(q^i, q^mu)$],
  $tilde(B)^i_mu$, [Internal coordinate Jacobian with respect to mass-weighted Cartesians,
  $tilde(B)^i_mu equiv physica.pdv(q^i, tilde(q)^mu)$],
  $tilde(C)^i_(mu nu)$, [Derivative of the mass-weighted internal coordinate Jacobian,
  $C^i_(mu nu) = physica.pdv(tilde(B)^i_mu, tilde(q)^nu) equiv physica.pdv(q^i, tilde(q)^mu, tilde(q)^nu)$],
)


#pagebreak()

== Proofs

#rect[
  #proposition(
    [
      $
      bold(e)_i
      = bold(e)_mu \(bold(T)\)^mu_i
      quad arrow.double quad
      q^i
      = \(bold(T)^(-1)\)^i_mu q^mu
      $
      By definition, this behavior bolds for all vectors and for all contravariant (upper index) tensor components.
    ],
    title: "Contravariance of coordinates",
    proof: [
      $q^mu bold(e)_mu
      = bold(q)
      = q^i bold(e)_i
      = q^i bold(e)_mu \(bold(T)\)^mu_i
      = \(bold(T)\)^mu_i q^i bold(e)_mu
      $.
      This implies
      $q^mu
      = \(bold(T)\)^mu_i q^i$,
      which leads to the final result:
      $\(bold(T)^(-1)\)^i_mu q^mu
      = \(bold(T)^(-1)\)^i_mu \(bold(T)\)^nu_j q^j
      = delta^i_j q^j
      = q^i$.
    ]
  ) <prop:contravariance-of-coordinates>
]


#rect[
  #proposition(
    [
      $
      bold(e)_i
      = bold(e)_mu \(bold(T)\)^mu_i
      quad arrow.double quad
      physica.pdv(f, q^i)
      = physica.pdv(f, q^mu) \(bold(T))^mu_i
      $
      By definition, this behavior bolds for all co-vectors and for all covariant (lower index) tensor components.
    ],
    title: "Covariance of derivatives",
    proof: [
      In @prop:contravariance-of-coordinates, it was proven that
      $q^mu
      = \(bold(T)\)^mu_i q^i$.
      The final result then follows from the chain rule:
      $physica.pdv(f, q^i)
      = physica.pdv(f, q^mu) physica.pdv(q^mu, q^i)
      = physica.pdv(f, q^mu) \(bold(T))^mu_j physica.pdv(q^j, q^i)
      = physica.pdv(f, q^mu) \(bold(T))^mu_j delta^j_i
      = physica.pdv(f, q^mu) \(bold(T))^mu_i$.
    ]
  ) <prop:covariance-of-derivatives>
]


#rect[
  #proposition(
    [
      $
      physica.iprod(bold(v), bold(w))
      = physica.iprod(bold(tilde(v)), bold(tilde(w)))
      = physica.iprod(bold(v)', bold(w)')
      quad quad
      physica.iprod(bold(alpha), bold(beta))
      = physica.iprod(bold(tilde(alpha)), bold(tilde(beta)))
      = physica.iprod(bold(alpha)', bold(beta)')
      $
      Since the vector and co-vector inner products are equivalent,
      we can simply write
      $physica.iprod(bold(v), bold(w))$
      and
      $physica.iprod(bold(alpha), bold(beta))$.
    ],
    title: "Invariance of inner products",
    proof: [
      Given a basis transformation
      $bold(e)_i
      = bold(e)_mu \(bold(T)\)^mu_i
      $,
      covariant quantities satisfy
      $alpha_i
      = alpha_mu \(bold(T)\)^mu_i$
      and contravariant quantities satisfy
      $v^mu
      = v^i \(bold(T)\)^mu_i$.
      This implies
      $physica.iprod(bold(v)', bold(w)')
      = G_(i j) v^i w^j
      = G_(mu nu) \(bold(T)\)^mu_i \(bold(T)\)^nu_j v^i w^j
      = G_(mu nu) v^mu w^nu
      = physica.iprod(bold(v), bold(w))$.
      The same logic holds for all of the other cases.
    ]
  ) <prop:inner-product-invariance>
]


#rect[
  #proposition(
    [
      The co- and contravariant metrics are inverses.
      $
      G_(j k) G^(k i)
      = G^(i k) G_(k j)
      = delta^i_j
      $
    ],
    title: "Co- and contravariant metrics",
    proof: [
      Let the $bold(e)_i$ basis be derived from an orthonormal basis $bold(e)_mu$ as
      $bold(e)_i
      = bold(e)_mu \(bold(T)\)^mu_i
      $.
      This is always possible by Gram-Schmidt orthogonalization with respect to the final metric $G_(i j)$.
      It follows that $G_(mu nu) = delta_(mu nu)$ and $G^(mu nu) = delta^(mu nu)$.
      This leads to the final result:
      $G_(j k) G^(k i)
      = G_(nu rho) G^(rho mu) \(bold(T)\)^nu_j \(bold(T)^(-1)\)^i_mu
      = delta_(nu rho) delta^(rho mu) \(bold(T)\)^nu_j \(bold(T)^(-1)\)^i_mu
      = \(bold(T)\)^mu_j \(bold(T)^(-1)\)^i_mu
      = delta^i_j
      $.
    ]
  ) <prop:co-and-contravariant-metrics>
]


#rect[
  #proposition(
    [
      Defining
      $T
      = 1/2 physica.iprod(dot(bold(q)), dot(bold(q)))
      $
      yields the following system of metrics.
      $
      G_(mu nu)
      = m_((mu)) delta_(mu nu)
      quad
      G^(mu nu)
      = m_((mu))^(-1) delta^(mu nu)
      quad
      tilde(G)_(mu nu)
      = delta_(mu nu)
      quad
      tilde(G)^(mu nu)
      = delta^(mu nu)
      quad
      G_(i j)
      = "inverse of"
      G^(i j)
      = delta^(mu nu) tilde(B)^i_mu tilde(B)^j_nu
      $
      In the last case, the given internal coordinate metric is only exact for infinitesimal displacements, $dif q^i$.
    ],
    title: "Kinetic energy metrics",
    proof: [
      For the Cartesian metric,
      $1/2 physica.iprod(dot(bold(q)), dot(bold(q)))
      = 1/2 G_(mu nu) dot(q)^mu dot(q)^nu
      = 1/2 m_((mu)) delta_(mu nu) dot(x)^mu dot(x)^nu
      = T$.
      By @prop:co-and-contravariant-metrics,
      the corresponding contravariant metric is
      $G^(mu nu) = m_((mu))^(-1) delta^(mu nu)$.
      By @prop:inner-product-invariance,
      the proof is completed by showing that this transforms into the other contravariant metrics.
      The transformation to mass-weighted Cartesians is
      $tilde(q)^mu = m_((mu))^(1/2) q^mu$,
      so the corresponding contravariant metric in mass-weighted coordinates is
      $tilde(G)^(mu nu)
      = m_((mu))^(1/2) m_((nu))^(1/2) G^(mu nu)
      = m_((mu))^(1/2) m_((nu))^(1/2) m_((mu))^(-1) delta^(mu nu)
      = m_((nu))^(1/2) m_((mu))^(-1/2) delta^(mu nu)
      = delta^(mu nu)
      $.
      The transformation from mass-weighted to internal coordinates is
      $q^i = tilde(B)^i_mu tilde(q)^mu + cal(O)(bold(tilde(q))^2)$,
      so the corresponding contravariant metric in internal coordinates is
      $G^(i j)
      = tilde(G)^(mu nu) tilde(B)^i_mu tilde(B)^j_nu
      = delta^(mu nu) tilde(B)^i_mu tilde(B)^j_nu
      $.
    ]
  ) <prop:kinetic-energy-metrics>
]


#rect[
  #proposition(
    [
      $
      q^i
      = tilde(B)^i_mu tilde(q)^mu
      + tilde(C)^i_(mu nu) tilde(q)^mu tilde(q)^nu
      + cal(O)(bold(tilde(q))^2)
      $
    ],
    title: "Internal coordinate Taylor expansion in mass-weighted Cartesian coordinates",
    proof: [
      This follows from writing the Taylor expansion of $q^i$ in terms of $tilde(B)^i_mu$ and $tilde(C)^i_(mu nu)$,
      as defined above.
    ]
  ) <prop:internal-coordinate-taylor-expansion>
]


#rect[
  #proposition(
    [
      $
      tilde(B)^i_rho tilde(A)^rho_j
      = delta^i_j
      quad quad
      tilde(A)^mu_i
      equiv
      delta^(mu rho) tilde(B)^k_rho G_(k i)
      $
    ],
    title: "Right pseudo-inverse of the B-matrix",
    proof: [
      By @prop:internal-coordinate-metric-tensor,
      $delta^i_j
      = G^(i k) G_(k j)
      = delta^(rho sigma) tilde(B)^i_rho tilde(B)^k_sigma G_(k j)
      = tilde(B)^i_rho tilde(A)^rho_j
      $.
    ]
  ) <prop:b-matrix-pseudoinverse>
]


#rect[
  #proposition(
    [
      The potential energy
      $V
      = V_0
      + g_mu q^mu
      + 1/2 H_(mu nu) q^mu q^nu
      + cal(O)(bold(q)^2)
      $
      can be expressed in the other coordinate systems by the following gradient and Hessian transformations.
      $
      V
      &= V_0
      + tilde(g)_mu tilde(q)^mu
      + 1/2 tilde(H)_(mu nu) tilde(q)^mu tilde(q)^nu
      + cal(O)(bold(tilde(q))^2)
      quad quad
      &tilde(g)_mu
      &= m_((mu))^(-1/2) g_mu
      quad quad
      &tilde(H)_(mu nu)
      &= m_((mu))^(-1/2) m_((nu))^(-1/2) H_(mu nu)
      \
      V
      &= V_0
      + g_i q^i
      + 1/2 H_(i j) q^i q^j
      + cal(O)(bold(q)'^2)
      quad quad
      &g_i
      &= tilde(g)_mu tilde(A)^mu_i
      quad quad
      &H_(i j)
      &= 
      (
        tilde(H)_(mu nu)
        - g_k tilde(C)^k_(mu nu)
      )
      tilde(A)^mu_i tilde(A)^nu_j
      $
    ],
    title: "Potential energy derivatives",
    proof: [
      Because mass-weighting is a linear transformation,
      the mass-weighted Cartesian gradient and Hessian can be obtained directly using
      $tilde(alpha)_mu = m_((mu))^(-1/2) alpha_mu$.
      The transformation to internal coordinates is non-linear and requires further consideration.
      First, substituting
      @prop:internal-coordinate-taylor-expansion
      into the internal coordinate Taylor expansion and collecting terms gives
      $V
      = g_i tilde(B)^i_mu tilde(q)^mu
      + 1/2 \(g_i tilde(C)^i_(mu nu) + H_(i j) tilde(B)^i_mu tilde(B)^j_nu\) tilde(q)^mu tilde(q)^nu
      + cal(O)(bold(tilde(q))^2)
      $.
      Comparing this to the mass-weighted Taylor expansion allows us to identify
      $tilde(g)_mu
      = g_i tilde(B)^i_mu
      $
      and
      $tilde(H)_(mu nu)
      = g_i tilde(C)^i_(mu nu)
      + H_(i j) tilde(B)^i_mu tilde(B)^j_nu
      $.
      Inverting these by @prop:b-matrix-pseudoinverse gives the result.
    ]
  ) <prop:potential-energy-derivatives>
]


#rect[
  #proposition(
    [
      $
      v^i w_i
      = physica.iprod(bold(v), bold(w))
      quad quad
      alpha_i beta^i
      = physica.iprod(bold(alpha), bold(beta))
      $
    ],
    title: "Dual vector contraction as inner product",
    proof: [
      By the definition of the dual vectors,
      $physica.iprod(bold(v), bold(w))
      = G_(i j) v^i w^j
      = v^i w_i
      $
      and
      $physica.iprod(bold(alpha), bold(beta))
      = G^(i j) alpha_i beta_j
      = alpha_i beta^i
      $.
    ]
  ) <prop:dual-vector-contraction-as-inner-product>
]


#rect[
  #proposition(
    [
      #footnote[An alternative approach takes this property as fundamental and derives @prop:co-and-contravariant-metrics from it.]
      $
      \(bold(v)^flat\)^sharp
      = bold(v)
      quad quad
      \(bold(alpha)^sharp\)^flat
      = bold(alpha)
      $
    ],
    title: "Dual vector consistency",
    proof: [
      By @prop:co-and-contravariant-metrics,
      $G^(i j) G_(j k) v^k
      = delta^i_k v^k
      = v^i
      $
      and
      $G_(i j) G^(j k) alpha_k
      = delta^k_i alpha_k
      = alpha_i$.
    ]
  ) <prop:dual-vector-consistency>
]


#rect[
  #proposition(
    [
      The projections onto $bold(v)$ and $bold(alpha)$ are as follows.
      $
      bold(P)_(bold(v))
      = frac(bold(v) times.o bold(v)^flat, physica.iprod(bold(v), bold(v)))
      quad
      (bold(P)_(bold(v)))^i_j
      = frac(v^i v_j, physica.iprod(bold(v), bold(v)))
      quad quad
      bold(P)_(bold(alpha))
      = frac(bold(alpha) times.o bold(alpha)^sharp, physica.iprod(bold(alpha), bold(alpha)))
      quad quad
      (bold(P)_(bold(alpha)))^i_j
      = frac(alpha_j alpha^i, physica.iprod(bold(alpha), bold(alpha)))
      $
    ],
    title: "Projection operator",
    proof: [
      By @prop:dual-vector-contraction-as-inner-product,
      $(bold(P)_bold(v) (bold(w)))^i
      = frac(v^i v_j, physica.iprod(bold(v), bold(v))) w^j
      = v^i frac(physica.iprod(bold(v), bold(w)), physica.iprod(bold(v), bold(v)))
      arrow.double
      bold(P)_bold(v) (bold(w))
      = bold(v) frac(physica.iprod(bold(v), bold(w)), physica.iprod(bold(v), bold(v)))
      $
      and
      $(bold(P)_bold(alpha) (bold(beta)))_j
      = frac(alpha_j alpha^i, physica.iprod(bold(alpha), bold(alpha))) beta_i
      = alpha_j frac(physica.iprod(bold(alpha), bold(beta)), physica.iprod(bold(alpha), bold(alpha)))
      arrow.double
      bold(P)_bold(alpha) (bold(beta))
      = bold(alpha) frac(physica.iprod(bold(alpha), bold(beta)), physica.iprod(bold(alpha), bold(alpha)))
      $.
      This is the standard form of a standard projection operator, albeit with a generalized inner product.
    ]
  ) <prop:dual-vector-consistency>
]





#pagebreak()

#rect[
  #proposition(
    [
      $
      tilde(v)_mu
      =
      v_k
      tilde(B)^k_mu
      $
    ],
    title: "Lemma: Internal to mass-weighted Cartesian coordinate co-vector transformation",
    proof: [
      The gradient $tilde(g)_mu = physica.pdv(V, tilde(x)^mu)$ is a co-vector, so all other co-vectors (and all lower indices) must transform like it.
      We can then prove this result by applying chain rule to the gradient:
      $physica.pdv(V, tilde(x)^mu)
      = physica.pdv(V, q^k) physica.pdv(q^k, tilde(x)^mu)
      $.
    ]
  ) <prop:internal-to-mass-weighted-cartesian-covector-transformation>
]


#rect[
  #proposition(
    [
      If $physica.iprod(dot, dot)_m$ is chosen as the inner product for Cartesian coordinates,
      then $physica.iprod(dot, dot)_1$ is the corresponding inner product for mass-weighted Cartesian coordinates
      and $physica.iprod(dot, dot)_G$ is the corresponding inner products for internal coordinates.
    ],
    title: "Kinetic Energy Metrics: Consistency",
    proof: [
      First, consider the mass-weighted Cartesian co-vector inner product
      $physica.iprod(tilde(bold(alpha)), tilde(bold(beta)))_1
      = tilde(alpha)_mu tilde(beta)_nu delta^(mu nu)
      = alpha^mu beta^nu m_((mu))^(-1/2) m_((nu))^(-1/2) delta^(mu nu)
      = alpha^mu beta^nu m_((mu)) delta^(mu nu)
      = alpha^mu beta^nu m_(mu nu)
      = physica.iprod(bold(alpha), bold(beta))_m
      $.
      Second, consider the internal coordinate co-vector inner product
      $physica.iprod(bold(alpha)', bold(beta)')_(G)
      = 
      $
    ]
  ) <prop:kinetic-energy-metrics-consistency>
]


#rect[
  #proposition(
    [
      $
      T
      = 1 / 2 physica.iprod(dot(bold(x)), dot(bold(x)))_m
      = 1 / 2 physica.iprod(tilde(dot(bold(x))), tilde(dot(bold(x))))_1
      = 1 / 2 physica.iprod(dot(bold(q)), dot(bold(q)))_(G)
      $
    ],
    title: "Kinetic Energy Metrics",
    proof: [
      The first expression is simply the definition of the kinetic energy,
      $T = 1/2 m_(mu nu) dot(x)^mu dot(x)^nu$.
      The other expressions then follow from the behavior of the metric under coordinate transformation.
    ]
  ) <prop:kinetic-energy>
]



#rect[
  #proposition(
    [
      $
      tilde(g)_mu
      =
      g_k tilde(B)^k_mu
      quad quad
      tilde(H)_(mu nu)
      = H_(k l) tilde(B)^k_mu tilde(B)^l_nu
      + g_k physica.pdv(q^k, tilde(x)^mu, tilde(x)^nu)
      $
    ],
    title: "Lemma: Cartesian Gradient and Hessian Taylor Expansion",
    proof: [
      The potential can be expressed in mass-weighted Cartesian coordinates as
      $V
      = V_0
      + tilde(g)_mu tilde(x)^mu
      + 1 / 2 tilde(H)_(mu nu) tilde(x)^mu tilde(x)^nu
      + cal(O)(bold(tilde(x))^2)
      $
      or in internal coordinates as
      $V
      = V_0
      + g_i q^i
      + 1 / 2 H_(i j) q^i q^j
      + cal(O)(bold(q)^2)
      $.
      Furthermore, the internal coordinates can be expanded in terms of mass-weighted Cartesian coordinates as
      $q^i
      = physica.pdv(q^i, tilde(x)^mu) tilde(x)^mu
      + 1/2 physica.pdv(q^i, tilde(x)^mu, tilde(x)^nu) tilde(x)^mu tilde(x)^nu
      + cal(O)(bold(x)^2)
      $.
      Substituting this into the second potential expression and comparing to the first gives the result.
    ]
  ) <prop:cartesian-gradient-and-hessian-expansion>
]


#rect[
  #proposition(
    [
      The covariant and contravariant internal coordinate metric can be defined relative to mas-weighted Cartesians as follows.
      $
      G_(j k)
      G^(k i)
      =
      G^(i k)
      G_(k j)
      =
      delta^i_j
      quad quad
      G^(i j)
      equiv
      delta^(rho sigma)
      tilde(B)^i_rho
      tilde(B)^j_sigma
      $
    ],
    title: "Internal Coordinate Metrics",
    proof: [
      Since Cartesian coordinates are rectilinear, their contravariant metric is
      $G^(rho sigma) = delta^(rho sigma)$.
      The formula for the contravariant internal coordinate metric therefore follows from @prop:metric-tensor-translation,
      and according to
      @prop:metric-tensor-inversion
      the covariant internal coordinate metric is then defined as the inverse of this.
    ]
  ) <prop:internal-coordinate-metric-tensor>
]


#rect[
  #proposition(
    [
      $
      tilde(B)^i_rho tilde(A)^rho_j
      = delta^i_j
      quad quad
      tilde(A)^mu_i
      equiv
      delta^(mu rho) tilde(B)^k_rho G_(k i)
      $
    ],
    title: "Lemma: Jacobian Right Pseudo-inverse",
    proof: [
      By @prop:internal-coordinate-metric-tensor,
      $delta^i_j
      = G^(i k) G_(k j)
      = delta^(rho sigma) tilde(B)^i_rho tilde(B)^k_sigma G_(k j)
      = tilde(B)^i_rho tilde(A)^rho_j
      $.
    ]
  ) <prop:jacobian-pseudo-inverse>
]



#rect[
  #proposition(
    [
      $
      g_i
      = tilde(g)_rho tilde(A)^rho_i
      quad quad
      H_(i j)
      = 
      (
        tilde(H)_(rho sigma)
        - g_k physica.pdv(q^k, tilde(x)^rho, tilde(x)^sigma)
      )
      tilde(A)^rho_i tilde(A)^sigma_j
      $
    ],
    title: "Internal Coordinate Gradient and Hessian",
    proof: [
      From @prop:cartesian-gradient-and-hessian-expansion
      and @prop:jacobian-pseudo-inverse,
      we have
      $tilde(g)_rho tilde(A)^rho_i
      = g_k tilde(B)^k_rho tilde(A)^rho_i
      = g_k delta^k_i
      = g_i
      $
      for the gradient and
      $tilde(H)_(rho sigma) tilde(A)^rho_i tilde(A)^sigma_j
      = H_(k l) tilde(B)^k_rho tilde(B)^l_sigma tilde(A)^rho_i tilde(A)^sigma_j
      + g_k physica.pdv(q^k, tilde(x)^rho, tilde(x)^sigma) tilde(A)^rho_i tilde(A)^sigma_j
      = H_(k l) delta^k_i delta^l_j
      + g_k physica.pdv(q^k, tilde(x)^rho, tilde(x)^sigma) tilde(A)^rho_i tilde(A)^sigma_j
      = H_(i j)
      + g_k physica.pdv(q^k, tilde(x)^rho, tilde(x)^sigma) tilde(A)^rho_i tilde(A)^sigma_j
      $.
    ]
  ) <prop:internal-coordinate-gradient-and-hessian>
]


= General Results


*Definitions*.
#table(
  columns: (auto, auto),
  stroke: none,
  $v_mu equiv g_(mu rho) v^rho$, [The "lowering" operation, which defines the dual of a vector],
  $v^mu equiv g^(mu rho) v_rho$, [This "raising" operation, which defines the contravariant metric]
)

#rect[
  #proposition(
    [
      $
      g^(mu rho) g_(rho nu)
      =
      g_(nu rho) g^(rho mu)
      =
      delta^mu_nu
      $
    ],
    title: "Co- and Contravariant Metrics are Inverses",
    proof: [
      Lowering and raising an arbitrary vector in sequence gives
      $v^mu = g^(mu rho) v_rho = g^(mu rho) g_(rho nu) v^nu$.
      This can only be satisfied if $g^(mu rho) g_(rho nu) = delta^mu_nu$.
      Doing the same starting from the dual vector $v_mu$ gives the second result.
    ]
  ) <prop:metric-tensor-inversion>
]

#rect[
  #proposition(
    [
      The translation of a metric tensor from coordinate system $x^mu$ to coordinate system $x'^mu$ is given by the following.
      $
      g_(mu nu)
      =
      g'_(rho sigma)
      physica.pdv(x'^rho, x^mu)
      physica.pdv(x'^sigma, x^nu)
      $
    ],
    title: "Metric Tensor Translation",
    proof: [
      Let $u$ and $v$ be arbitrary tangent vectors. By invariance of the inner product:
      $g_(mu nu) u^mu v^nu
      =
      physica.innerproduct(bold(u), bold(v))
      =
      g'_(alpha beta)
      u'^alpha
      v'^beta
      =
      g'_(alpha beta)
      physica.pdv(x'^alpha, x^mu)
      physica.pdv(x'^beta, x^nu)
      u^mu v^nu
      $.
      Since the vector components $u^mu$ and $v^nu$ are arbitrary, this implies:
      $g_(mu nu)
      =
      g'_(alpha beta)
      physica.pdv(x'^alpha, x^mu)
      physica.pdv(x'^beta, x^nu)
      $.
    ]
  ) <prop:metric-tensor-translation>
]
